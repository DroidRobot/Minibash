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

/* These are field ids suitable for use in ts_node_child_by_field_id for certain rules. 
   e.g., to obtain the body of a while loop, you can use:
    TSNode body = ts_node_child_by_field_id(child, bodyId);
*/
static TSFieldId bodyId, redirectId, destinationId, valueId, nameId, conditionId;
static TSFieldId variableId;
static TSFieldId leftId, operatorId, rightId;

static char *input;         // to avoid passing the current input around
static TSParser *parser;    // a singleton parser instance 
static tommy_hashdyn shell_vars;        // a hash table containing the internal shell variables
static int last_exit_status = 0;   // global last exit status

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

/* Build a prompt */
static char *
build_prompt(void)
{
    return strdup("minibash> ");
}

/* Possible job status's to use.
 *
 * Some are specific to interactive job control which may not be needed
 * for this assignment.
 */
enum job_status {
    FOREGROUND,     /* job is running in foreground.  Only one job can be
                       in the foreground state. */
    BACKGROUND,     /* job is running in background */
    STOPPED,        /* job is stopped via SIGSTOP */
    NEEDSTERMINAL,  /* job is stopped because it was a background job
                       and requires exclusive terminal access */
    TERMINATED_VIA_EXIT,    /* job terminated via normal exit. */
    TERMINATED_VIA_SIGNAL   /* job terminated via signal. */
};

struct job {
    struct list_elem elem;   /* Link element for jobs list. */
    int     jid;             /* Job id. */
    enum job_status status;  /* Job status. */ 
    int  num_processes_alive;   /* The number of processes that we know to be alive */
    pid_t pgid; /* need to map job to its child process*/
    int exit_status;
    /* Add additional fields here as needed. */
};

/* Utility functions for job list management.
 * We use 2 data structures: 
 * (a) an array jid2job to quickly find a job based on its id
 * (b) a linked list to support iteration
 */
#define MAXJOBS (1<<16)
static struct list job_list;

static struct job *jid2job[MAXJOBS];

/* Return job corresponding to jid */
static struct job *
get_job_from_jid(int jid)
{
    if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL)
        return jid2job[jid];

    return NULL;
}

/* Allocate a new job, optionally adding it to the job list. */
static struct job *
allocate_job(bool includeinjoblist)
{
    struct job * job = malloc(sizeof *job);
    job->num_processes_alive = 0;
    job->jid = -1;
    job->pgid = 0;
    job->exit_status = 0;
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

/* Delete a job.
 * This should be called only when all processes that were
 * forked for this job are known to have terminated.
 */
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
    /* add any other job cleanup here. */
    free(job);
}


/*
 * Suggested SIGCHLD handler.
 *
 * Call waitpid() to learn about any child processes that
 * have exited or changed status (been stopped, needed the
 * terminal, etc.)
 * Just record the information by updating the job list
 * data structures.  Since the call may be spurious (e.g.
 * an already pending SIGCHLD is delivered even though
 * a foreground process was already reaped), ignore when
 * waitpid returns -1.
 * Use a loop with WNOHANG since only a single SIGCHLD 
 * signal may be delivered for multiple children that have 
 * exited. All of them need to be reaped.
 */
static void
sigchld_handler(int sig, siginfo_t *info, void *_ctxt)
{
    pid_t child;
    int status;
    assert(sig == SIGCHLD);
    while ((child = waitpid(-1, &status, WUNTRACED|WNOHANG)) > 0) {
        handle_child_status(child, status);
    }
}

/* Wait for all processes in this job to complete, or for
 * the job no longer to be in the foreground.
 *
 * You should call this function from where you wait for
 * jobs started without the &; you would only use this function
 * if you were to implement the 'fg' command (job control only).
 * 
 * Implement handle_child_status such that it records the 
 * information obtained from waitpid() for pid 'child.'
 *
 * If a process exited, it must find the job to which it
 * belongs and decrement num_processes_alive.
 *
 * However, note that it is not safe to call delete_job
 * in handle_child_status because wait_for_job assumes that
 * even jobs with no more num_processes_alive haven't been
 * deallocated.  You should postpone deleting completed
 * jobs from the job list until when your code will no
 * longer touch them.
 *
 * The code below relies on `job->status` having been set to FOREGROUND
 * and `job->num_processes_alive` having been set to the number of
 * processes successfully forked for this job.
 */
static void
wait_for_job(struct job *job)
{
    assert(signal_is_blocked(SIGCHLD));

    while (job->status == FOREGROUND && job->num_processes_alive > 0) {
        int status;

        pid_t child = waitpid(-1, &status, WUNTRACED);

        // When called here, any error returned by waitpid indicates a logic
        // bug in the shell.
        // In particular, ECHILD "No child process" means that there has
        // already been a successful waitpid() call that reaped the child, so
        // there's likely a bug in handle_child_status where it failed to update
        // the "job" status and/or num_processes_alive fields in the required
        // fashion.
        // Since SIGCHLD is blocked, there cannot be races where a child's exit
        // was handled via the SIGCHLD signal handler.
        if (child != -1)
            handle_child_status(child, status);
        else
            utils_fatal_error("waitpid failed, see code for explanation");
    }
}

static struct job *
find_job_by_pid(pid_t pid)
{
    struct list_elem *e;
    for (e = list_begin(&job_list); e != list_end(&job_list); e = list_next(e)) {
        struct job *j = list_entry(e, struct job, elem);
        /* For a single-process job, pgid == the child's pid.
         * For a pipeline, pgid == the first child's pid.
         * Either way, check if this pid belongs to the group. */
        if (j->pgid == pid)
            return j;
        /* Also check via getpgid in case the process is still alive */
        pid_t pg = getpgid(pid);
        if (pg != -1 && pg == j->pgid)
            return j;
    }
    return NULL;
}
/*
 * handle_child_status — called from both the SIGCHLD handler and
 * wait_for_job whenever waitpid() reports a status change.
 *
 * Steps:
 *   1. Find which job this pid belongs to (via pgid).
 *   2. Check what happened using WIF* macros.
 *   3. Update job->exit_status and job->num_processes_alive.
 *      If all processes in the job are dead, mark it terminated.
 */
static void
handle_child_status(pid_t pid, int status)
{
    assert(signal_is_blocked(SIGCHLD));

    struct job *job = find_job_by_pid(pid);
    if (job == NULL)
        return;

    if (WIFEXITED(status)) {
        /* Process exited normally via exit() or returning from main() */
        job->exit_status = WEXITSTATUS(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0)
            job->status = TERMINATED_VIA_EXIT;

    } else if (WIFSIGNALED(status)) {
        /* Process was killed by a signal (e.g. SIGKILL, SIGSEGV) */
        /* bash convention: $? = 128 + signal_number */
        job->exit_status = 128 + WTERMSIG(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0)
            job->status = TERMINATED_VIA_SIGNAL;

    } else if (WIFSTOPPED(status)) {
        /* Process was stopped (Ctrl-Z etc.) — not tested, but handle it */
        job->status = STOPPED;
    }
}


/* =========================================================================
 * Phase 1: plain words only
 *
 * expand_node takes a tree-sitter node and returns the string it
 * represents at runtime.  In Phase 1, the only node type we handle
 * is a plain "word" — we just copy the raw source text.
 *
 * Every other node type falls through to the raw-text fallback so
 * the shell at least produces some output rather than crashing.
 * ========================================================================= */

static char *
expand_node(TSNode node)
{
    if (ts_node_is_null(node))
        return strdup("");

    const char *type = ts_node_type(node);

    /* Plain unquoted word: "echo", "hello", "/bin/ls", etc.
     * ts_extract_node_text copies the raw source bytes for this node.
     * The caller owns the returned string and must free() it. */
    if (strcmp(type, "word") == 0) {
        return ts_extract_node_text(input, node);
    }

    /* command_name wraps the actual word in a named child */
    if (strcmp(type, "command_name") == 0) {
        uint32_t nc = ts_node_named_child_count(node);
        if (nc > 0)
            return expand_node(ts_node_named_child(node, 0));
        return ts_extract_node_text(input, node);
    }

    /* Fallback for anything we haven't implemented yet:
     * return the raw source text so things don't crash. */
    return ts_extract_node_text(input, node);
}

/* =========================================================================
 * build_argv
 *
 * Walk the named children of a "command" node and build a
 * NULL-terminated argv array suitable for posix_spawnp().
 *
 * A command node looks like:
 *   command
 *     command_name   ← argv[0]
 *     word           ← argv[1]
 *     word           ← argv[2]
 *     ...
 *
 * The caller must free each string and then the array itself.
 * Use free_argv() for convenience.
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

        /* Skip redirect nodes — not implemented yet in Phase 1 */
        if (strcmp(ctype, "file_redirect") == 0)
            continue;

        /* command_name becomes argv[0] */
        if (strcmp(ctype, "command_name") == 0) {
            if (argc >= capacity - 1) {
                capacity *= 2;
                argv = realloc(argv, capacity * sizeof(char *));
            }
            argv[argc++] = expand_node(child);
            continue;
        }

        /* All other named children are arguments */
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
 *
 * Returns true if the command was a builtin and we handled it.
 * Sets last_exit_status as appropriate.
 * ========================================================================= */

static bool
try_builtin(char **argv)
{
    if (argv[0] == NULL)
        return false;

    /* exit [code] — terminate the shell */
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
        }
        else {
            last_exit_status = 0;
        }
        return true;
    }

    return false;
}



/* =========================================================================
 * run_simple_command
 *
 * Execute a single external command using posix_spawnp().
 *
 * Key ideas:
 *   - posix_spawnp searches PATH for the program, just like execvp().
 *   - POSIX_SPAWN_SETPGROUP gives the child its own process group.
 *     We pass pgid=0 which means "use the child's own PID as group ID."
 *     This is required even for single-process jobs per the spec.
 *   - We then wait for it synchronously (foreground).
 * ========================================================================= */

static int
run_simple_command(TSNode node)
{
    char **argv = build_argv(node);

    if (argv[0] == NULL) {
        free_argv(argv);
        return 0;
    }

    /* Check builtins before trying to spawn */
    if (try_builtin(argv)) {
        free_argv(argv);
        return last_exit_status;
    }

    /* Set up posix_spawn attributes */
    posix_spawn_file_actions_t fa;
    posix_spawnattr_t attr;

    if (posix_spawn_file_actions_init(&fa) != 0)
        utils_fatal_error("posix_spawn_file_actions_init");
    if (posix_spawnattr_init(&attr) != 0)
        utils_fatal_error("posix_spawnattr_init");

    /* Give the child its own process group (pgid=0 → use child's own PID) */
    if (posix_spawnattr_setpgroup(&attr, 0) != 0)
        utils_fatal_error("posix_spawnattr_setpgroup");

    /* POSIX_SPAWN_SETPGROUP: actually apply the pgroup setting above.
     * POSIX_SPAWN_USEVFORK: use vfork() internally for speed (Linux extension). */
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
        /* posix_spawnp failed — program not found or exec error */
        fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(rc));
        free_argv(argv);
        last_exit_status = 127;
        return 127;
    }

    free_argv(argv);

    /* Register this child as a foreground job so handle_child_status
     * can find it when waitpid() reports its exit. */
    struct job *job = allocate_job(true);
    job->status = FOREGROUND;
    job->pgid = child;          /* single-process job: pgid == child pid */
    job->num_processes_alive = 1;

    /* Block SIGCHLD while we wait so the signal handler and wait_for_job
     * don't both try to reap the same child. */
    wait_for_job(job);
    last_exit_status = job->exit_status;
    delete_job(job, true);

    return last_exit_status;
}


/*
 * Run a program.
 *
 * A program's named children are various types of statements which 
 * you can start implementing here.
 */
static void 
run_program(TSNode program)
{
    /*
     * Steps
     * Extract arguments - iterator over child and extract with ts_extract_node_text()
     * Build argv
     * Handle quotes
     * Track jobs - allocate new job using allocate_job(true)
     * Execution: call posix_spawn()
     * wait for it to be done: wait_for_job()
     * delete_job()
     *
     */
    uint32_t count = ts_node_named_child_count(program);
    for (uint32_t i = 0; i < count; i++) {
        TSNode child = ts_node_named_child(program, i);
        const char *type = ts_node_type(child);
        // printf("Type: %s\n",type);

        if (strcmp(type, "comment") == 0) {
            /* Ignore comments */
            continue;
        }

        if (strcmp(type, "command") == 0) {
            run_simple_command(child);
            continue;
        }

        /* Everything else is not yet implemented */
        fprintf(stderr, "minibash: node type '%s' not yet implemented\n", type);

        // if(strcmp(type, "command") == 0){
        //     //extract the arguments
        //     // char *cmd_name = ts_extract_node_text(input, child);
        //     uint32_t numChild = ts_node_named_child_count(child);
        //     char **args = malloc(sizeof(char*) * (numChild+1));//+1 to NULL terminate
        //     //build argv
        //     for(int i = 0;i<numChild;i++){
        //         TSNode arg_node = ts_node_named_child(child,i);
        //         args[i] = ts_extract_node_text(input, arg_node);
        //     }
        //     args[numChild] = NULL;//null terminate for posix_spawnp

        //     // args[0] = cmd_name;

        //     //handle quotes here?

        //     //allocate_job
        //     struct job *thisJob = allocate_job(true);
        //     (*thisJob).status = FOREGROUND;
        //     (*thisJob).num_processes_alive = 1;

        //     int pid;
        //     int result = posix_spawnp(&pid, args[0], NULL, NULL, args, NULL);
            



        //     //wait for thisJob to be done call wait_for_thisJob()


        //     if(result == 0){
        //         thisJob->pid = pid;
        //         wait_for_job(thisJob);
        //     }else{
        //         perror("posix_spawnp didnt work");
        //         thisJob->num_processes_alive--;
        //     }

        //     //cleanup memory
        //     delete_job(thisJob, true);
        //     for(int i = 0;i<numChild;i++){
        //         free(args[i]);//free text returned by ts_extract_node_text
        //     }
        //     free(args);//free from malloc^^^^

        // }else{
        //     printf("node type `%s` not implemented\n", ts_node_type(child));
        // }
    }
}

/*
 * Read a script from this (already opened) file descriptor,
 * return a newly allocated buffer.
 */
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

/* 
 * Execute the script whose content is provided in `script`
 */
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

    /* Process command-line arguments. See getopt(3) */
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


    /* Read/eval loop. */
    bool shouldexit = false;
    for (;;) {
        if (shouldexit)
            break;

        /* If you fail this assertion, you were about to enter readline()
         * while SIGCHLD is blocked.  This means that your shell would be
         * unable to receive SIGCHLD signals, and thus would be unable to
         * wait for background jobs that may finish while the
         * shell is sitting at the prompt waiting for user input.
         */
        assert(!signal_is_blocked(SIGCHLD));

        char *userinput = NULL;
        /* Do not output a prompt unless shell's stdin is a terminal */
        if (isatty(0) && av[optind] == NULL) {
            char *prompt = isatty(0) ? build_prompt() : NULL;
            userinput = readline(prompt);
            free (prompt);
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

    /* 
     * Even though it is not necessary for the purposes of resource
     * reclamation, we free all allocated data structure prior to exiting
     * so that we can use valgrind's leak checker.
     */
    ts_parser_delete(parser);
    tommy_hashdyn_foreach(&shell_vars, hash_free);
    tommy_hashdyn_done(&shell_vars);
    return EXIT_SUCCESS;
}
