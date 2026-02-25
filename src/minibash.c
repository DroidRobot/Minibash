/*
 * minibash - an open-ended subset of bash
 *
 * Developed by Godmar Back for CS 3214 Fall 2025 
 * Virginia Tech.
 */
#define _GNU_SOURCE    1
#include <stdio.h>
#include <readline/readline.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <termios.h>
#include <sys/wait.h>
#include <assert.h>
#include <spawn.h>
#include <errno.h>
#include <stdbool.h>

#include <tree_sitter/api.h>
#include "tree_sitter/tree-sitter-bash.h"
#include "ts_symbols.h"
/* Since the handed out code contains a number of unused functions. */
#pragma GCC diagnostic ignored "-Wunused-function"

#include "hashtable.h"
#include "signal_support.h"
#include "utils.h"
#include "list.h"
#include "ts_helpers.h"

extern char **environ;

static TSFieldId bodyId, redirectId, destinationId, valueId, nameId, conditionId;
static TSFieldId variableId;
static TSFieldId leftId, operatorId, rightId;

static char *input;
static TSParser *parser;
static tommy_hashdyn shell_vars;
static int last_exit_status = 0;

static void handle_child_status(pid_t pid, int status);
static char *read_script_from_fd(int readfd);
static void execute_script(char *script);

static void
usage(char *progname)
{
    printf("Usage: %s -h\n"
        " -h            print this help\n",
        progname);
    exit(EXIT_SUCCESS);
}

static char *
build_prompt(void)
{
    return strdup("minibash> ");
}

enum job_status {
    FOREGROUND,
    BACKGROUND,
    STOPPED,
    NEEDSTERMINAL,
    TERMINATED_VIA_EXIT,
    TERMINATED_VIA_SIGNAL
};

struct job {
    struct list_elem elem;
    int     jid;
    enum job_status status;
    int  num_processes_alive;
    pid_t pgid;
    int exit_status;
    /*
     * pid array: store every spawned pid at spawn time so
     * find_job_by_pid never has to call getpgid() on a dead process.
     * Supports pipelines up to 64 commands wide.
     */
    pid_t pids[64];
    int   npids;
};

#define MAXJOBS (1<<16)
static struct list job_list;
static struct job *jid2job[MAXJOBS];

static struct job *
get_job_from_jid(int jid)
{
    if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL)
        return jid2job[jid];
    return NULL;
}

static struct job *
allocate_job(bool includeinjoblist)
{
    struct job *job = malloc(sizeof *job);
    job->num_processes_alive = 0;
    job->jid = -1;
    job->pgid = 0;
    job->exit_status = 0;
    job->npids = 0;
    if (!includeinjoblist)
        return job;

    list_push_back(&job_list, &job->elem);
    for (int i = 1; i < MAXJOBS; i++) {
        if (jid2job[i] == NULL) {
            jid2job[i] = job;
            job->jid = i;
            return job;
        }
    }
    fprintf(stderr, "Maximum number of jobs exceeded\n");
    abort();
    return NULL;
}

static void
delete_job(struct job *job, bool removeFromJobList)
{
    if (removeFromJobList) {
        int jid = job->jid;
        assert(jid != -1);
        assert(jid2job[jid] == job);
        jid2job[jid]->jid = -1;
        jid2job[jid] = NULL;
        list_remove(&job->elem);
    } else {
        assert(job->jid == -1);
    }
    free(job);
}

static void
sigchld_handler(int sig, siginfo_t *info, void *_ctxt)
{
    pid_t child;
    int status;
    assert(sig == SIGCHLD);
    while ((child = waitpid(-1, &status, WUNTRACED|WNOHANG)) > 0)
        handle_child_status(child, status);
}

static void
wait_for_job(struct job *job)
{
    assert(signal_is_blocked(SIGCHLD));
    while (job->status == FOREGROUND && job->num_processes_alive > 0) {
        int status;
        pid_t child = waitpid(-1, &status, WUNTRACED);
        if (child != -1)
            handle_child_status(child, status);
        else
            utils_fatal_error("waitpid failed, see code for explanation");
    }
}

/*
 * find_job_by_pid
 *
 * Scans the pid array stored in each job.
 * Pids are recorded at spawn time (before any process can exit),
 * so this never needs to call getpgid() on a potentially-dead process.
 * Works for single commands (1 pid) and pipelines (N pids) equally.
 */
static struct job *
find_job_by_pid(pid_t pid)
{
    struct list_elem *e;
    for (e = list_begin(&job_list); e != list_end(&job_list); e = list_next(e)) {
        struct job *j = list_entry(e, struct job, elem);
        for (int i = 0; i < j->npids; i++) {
            if (j->pids[i] == pid)
                return j;
        }
    }
    return NULL;
}

/*
 * handle_child_status
 *
 * Called from both sigchld_handler and wait_for_job whenever
 * waitpid() reports a status change.
 */
static void
handle_child_status(pid_t pid, int status)
{
    assert(signal_is_blocked(SIGCHLD));

    struct job *job = find_job_by_pid(pid);
    if (job == NULL)
        return;

    if (WIFEXITED(status)) {
        job->exit_status = WEXITSTATUS(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0)
            job->status = TERMINATED_VIA_EXIT;

    } else if (WIFSIGNALED(status)) {
        job->exit_status = 128 + WTERMSIG(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0)
            job->status = TERMINATED_VIA_SIGNAL;

    } else if (WIFSTOPPED(status)) {
        job->status = STOPPED;
    }
}

/* =========================================================================
 * expand_node — Phase 1: plain words only
 * ========================================================================= */

static char *
expand_node(TSNode node)
{
    if (ts_node_is_null(node))
        return strdup("");

    const char *type = ts_node_type(node);

    if (strcmp(type, "word") == 0)
        return ts_extract_node_text(input, node);

    if (strcmp(type, "command_name") == 0) {
        uint32_t nc = ts_node_named_child_count(node);
        if (nc > 0)
            return expand_node(ts_node_named_child(node, 0));
        return ts_extract_node_text(input, node);
    }

    return ts_extract_node_text(input, node);
}

/* =========================================================================
 * build_argv
 * ========================================================================= */

static char **
build_argv(TSNode cmd_node)
{
    int capacity = 8;
    int argc = 0;
    char **argv = malloc(capacity * sizeof(char *));

    uint32_t nc = ts_node_named_child_count(cmd_node);
    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_named_child(cmd_node, i);
        const char *ctype = ts_node_type(child);

        if (strcmp(ctype, "file_redirect") == 0) {
            // TODO: implement redirection (> < >> 2> >&)

            // set input and output files so we read and write to the approprate files in run_simple_command
        }
            

        if (argc >= capacity - 1) {
            capacity *= 2;
            argv = realloc(argv, capacity * sizeof(char *));
        }
        argv[argc++] = expand_node(child);
    }

    argv[argc] = NULL;
    return argv;
}

static void
free_argv(char **argv)
{
    if (!argv) return;
    for (int i = 0; argv[i] != NULL; i++)
        free(argv[i]);
    free(argv);
}

/* =========================================================================
 * Builtins
 * ========================================================================= */

static bool
try_builtin(char **argv)
{
    if (argv[0] == NULL)
        return false;

    if (strcmp(argv[0], "exit") == 0) {
        int code = argv[1] ? atoi(argv[1]) : 0;
        ts_parser_delete(parser);
        tommy_hashdyn_foreach(&shell_vars, hash_free);
        tommy_hashdyn_done(&shell_vars);
        exit(code);
    }

    if (strcmp(argv[0], "cd") == 0) {
        const char *dir = argv[1] ? argv[1] : (getenv("HOME") ? getenv("HOME") : "/");
        if (chdir(dir) != 0) {
            utils_error("cd: %s: ", dir);
            last_exit_status = 1;
        } else {
            last_exit_status = 0;
        }
        return true;
    }

    return false;
}

static bool
run_redirected_statement(TSNode node, posix_spawn_file_actions_t *fa)
{
    if (ts_node_is_null(node))
        return false;

    const char *type = ts_node_type(node);
    if (strcmp(type, "file_redirect") != 0)
        return false;

    TSNode dest = ts_node_child_by_field_name(node, "destination", strlen("destination"));
    TSNode value = ts_node_child_by_field_name(node, "value", strlen("value"));

    if (ts_node_is_null(dest) || ts_node_is_null(value))
        return false;

    char *dest_str = expand_node(dest);
    char *value_str = expand_node(value);

    int fd = -1;
    if (strcmp(dest_str, "stdin") == 0)
        fd = STDIN_FILENO;
    else if (strcmp(dest_str, "stdout") == 0)
        fd = STDOUT_FILENO;
    else if (strcmp(dest_str, "stderr") == 0)
        fd = STDERR_FILENO;
    else {
        free(dest_str);
        free(value_str);
        return false;
    }

    int rc = posix_spawn_file_actions_addopen(fa, fd, value_str, O_RDONLY, 0);
    free(dest_str);
    free(value_str);

    return rc == 0;
}

/* =========================================================================
 * run_simple_command
 *
 * Executes a single external command using posix_spawnp().
 *
 * Steps:
 *   1. Build argv from the tree node using build_argv()
 *   2. Check if the command is a builtin (cd, exit) and handle it
 *      directly in the shell process without spawning a child.
 *   3. Spawn the child process using posix_spawnp():
 *        - posix_spawn_file_actions_init(&fa)
 *            Creates an empty to-do list of fd operations the child
 *            will perform before exec (used for redirection in Phase 3).
 *        - posix_spawnattr_init(&attr)
 *            Creates an empty attributes struct to configure the child.
 *        - posix_spawnattr_setpgroup(&attr, 0)
 *            pgid=0 means "use the child's own PID as its process group ID",
 *            giving the child its own process group. Required by the spec
 *            even for single commands.
 *        - posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETPGROUP)
 *            Without this flag, setpgroup above does nothing. You must
 *            explicitly opt in to each attribute you want applied.
 *        - posix_spawnp(&child, argv[0], &fa, &attr, argv, environ)
 *            The actual spawn. Searches PATH for argv[0], applies fa and
 *            attr in the child, and writes the child's PID into child.
 *        - posix_spawn_file_actions_destroy(&fa)
 *        - posix_spawnattr_destroy(&attr)
 *            Every init must have a matching destroy or valgrind will
 *            report memory leaks and you lose points.
 *   4. Register the child as a foreground job, record its pid in
 *      job->pids[] so find_job_by_pid() can locate it after it exits,
 *      then wait for it to finish and clean up.
 *
 * ========================================================================= */

static int
run_simple_command(TSNode node, posix_spawn_file_actions_t *fa)
{
    char **argv = build_argv(node);

    if (argv[0] == NULL) {
        free_argv(argv);
        return 0;
    }

    if (try_builtin(argv)) {
        free_argv(argv);
        return last_exit_status;
    }

    // posix_spawn_file_actions_t fa;
    posix_spawnattr_t attr;

    // if (posix_spawn_file_actions_init(&fa) != 0)
    //     utils_fatal_error("posix_spawn_file_actions_init");
    if (posix_spawnattr_init(&attr) != 0)
        utils_fatal_error("posix_spawnattr_init");

    if (posix_spawnattr_setpgroup(&attr, 0) != 0)
        utils_fatal_error("posix_spawnattr_setpgroup");

    int flags = POSIX_SPAWN_SETPGROUP;
#ifdef POSIX_SPAWN_USEVFORK
    flags |= POSIX_SPAWN_USEVFORK;
#endif
    if (posix_spawnattr_setflags(&attr, flags) != 0)
        utils_fatal_error("posix_spawnattr_setflags");

    pid_t child;
    int rc = posix_spawnp(&child, argv[0], &fa, &attr, argv, environ);

    if (posix_spawn_file_actions_destroy(&fa) != 0)
        utils_error("posix_spawn_file_actions_destroy");
    if (posix_spawnattr_destroy(&attr) != 0)
        utils_error("posix_spawnattr_destroy");

    if (rc != 0) {
        fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(rc));
        free_argv(argv);
        last_exit_status = 127;
        return 127;
    }

    free_argv(argv);

    struct job *job = allocate_job(true);
    job->status = FOREGROUND;
    job->pgid = child;
    job->num_processes_alive = 1;
    job->pids[job->npids++] = child;   /* record pid so find_job_by_pid works */

    wait_for_job(job);
    last_exit_status = job->exit_status;
    delete_job(job, true);

    return last_exit_status;
}

/* =========================================================================
 * run_program
 * ========================================================================= */

static void
run_program(TSNode program)
{
    uint32_t count = ts_node_named_child_count(program);
    for (uint32_t i = 0; i < count; i++) {
        TSNode child = ts_node_named_child(program, i);
        const char *type = ts_node_type(child);

        if (strcmp(type, "comment") == 0)
            continue;

        if (strcmp(type, "command") == 0) {
            run_simple_command(child);
            continue;
        }

        if (strcmp(type, "pipeline") == 0) {
            /*
             * TODO: implement pipeline support
             *
             * Friend's pipeline stub (starting point):
             *
             * uint32_t numChild = ts_node_named_child_count(child);
             *
             * struct job *thisJob = allocate_job(true);
             * thisJob->status = FOREGROUND;
             * thisJob->num_processes_alive = 0;
             *
             * int stdin_fd = STDIN_FILENO;
             *
             * // ls | cat
             * // stdout of ls goes into stdin of cat
             * for (int i = 0; i < numChild; i++) {
             *     TSNode currNode = ts_node_named_child(child, i);
             *     char **args = build_argv(currNode);
             *
             *     int pipefd[2];
             *     posix_spawn_file_actions_t actions;
             *     posix_spawn_file_actions_init(&actions);
             *
             *     if (stdin_fd != STDIN_FILENO) {
             *         // wire previous pipe's read end to stdin
             *         posix_spawn_file_actions_adddup2(&actions, stdin_fd, STDIN_FILENO);
             *     }
             *     if (i < numChild - 1) {
             *         // not last command: create pipe and wire stdout to write end
             *         pipe(pipefd);
             *         posix_spawn_file_actions_adddup2(&actions, pipefd[1], STDOUT_FILENO);
             *         stdin_fd = pipefd[0];  // next command reads from here
             *     }
             *
             *     int pid;
             *     int result = posix_spawnp(&pid, args[0], &actions, NULL, args, NULL);
             *     posix_spawn_file_actions_destroy(&actions);
             *
             *     if (result == 0) {
             *         thisJob->num_processes_alive++;
             *         // TODO: record pid, set pgid, close pipe fds in parent
             *     }
             * }
             *
             * wait_for_job(thisJob);
             * delete_job(thisJob, true);
             */
            fprintf(stderr, "minibash: pipeline not yet implemented\n");
            continue;
        }

        if (strcmp(type, "redirected_statement") == 0) {
            /* TODO: implement redirection (> < >> 2> >&) */
            run_redirected_statement(ts_node_child_by_field_name(child, "redirect", strlen("redirect")), NULL);
            fprintf(stderr, "minibash: redirection not yet implemented\n");
            continue;
        }

        fprintf(stderr, "minibash: node type '%s' not yet implemented\n", type);
    }
}

static char *
read_script_from_fd(int readfd)
{
    struct stat st;
    if (fstat(readfd, &st) != 0) {
        utils_error("Could not fstat input");
        return NULL;
    }

    char *userinput = malloc(st.st_size+1);
    if (read(readfd, userinput, st.st_size) != st.st_size) {
        utils_error("Could not read input");
        free(userinput);
        return NULL;
    }
    userinput[st.st_size] = 0;
    return userinput;
}

static void
execute_script(char *script)
{
    input = script;
    TSTree *tree = ts_parser_parse_string(parser, NULL, input, strlen(input));
    TSNode  program = ts_tree_root_node(tree);
    signal_block(SIGCHLD);
    run_program(program);
    signal_unblock(SIGCHLD);
    ts_tree_delete(tree);
}

int
main(int ac, char *av[])
{
    int opt;
    tommy_hashdyn_init(&shell_vars);

    while ((opt = getopt(ac, av, "h")) > 0) {
        switch (opt) {
        case 'h':
            usage(av[0]);
            break;
        }
    }

    parser = ts_parser_new();
    const TSLanguage *bash = tree_sitter_bash();
#define DEFINE_FIELD_ID(name) \
    name##Id = ts_language_field_id_for_name(bash, #name, strlen(#name))
    DEFINE_FIELD_ID(body);
    DEFINE_FIELD_ID(condition);
    DEFINE_FIELD_ID(name);
    DEFINE_FIELD_ID(right);
    DEFINE_FIELD_ID(left);
    DEFINE_FIELD_ID(operator);
    DEFINE_FIELD_ID(value);
    DEFINE_FIELD_ID(redirect);
    DEFINE_FIELD_ID(destination);
    DEFINE_FIELD_ID(variable);
    ts_parser_set_language(parser, bash);

    list_init(&job_list);
    signal_set_handler(SIGCHLD, sigchld_handler);

    bool shouldexit = false;
    for (;;) {
        if (shouldexit)
            break;

        assert(!signal_is_blocked(SIGCHLD));

        char *userinput = NULL;
        if (isatty(0) && av[optind] == NULL) {
            char *prompt = isatty(0) ? build_prompt() : NULL;
            userinput = readline(prompt);
            free(prompt);
            if (userinput == NULL)
                break;
        } else {
            int readfd = 0;
            if (av[optind] != NULL)
                readfd = open(av[optind], O_RDONLY);
            userinput = read_script_from_fd(readfd);
            close(readfd);
            if (userinput == NULL)
                utils_fatal_error("Could not read input");
            shouldexit = true;
        }
        execute_script(userinput);
        free(userinput);
    }

    ts_parser_delete(parser);
    tommy_hashdyn_foreach(&shell_vars, hash_free);
    tommy_hashdyn_done(&shell_vars);
    return EXIT_SUCCESS;
}