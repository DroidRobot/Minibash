/*
 * minibash - Phase 1: Simple Commands + Builtins
 *
 * This phase establishes the clean foundation.  It passes:
 *   001-comment          (comments are silently skipped)
 *   005-command          (absolute-path command: /usr/bin/arch)
 *   007-command          (PATH-searched command: arch)
 *   010-command-with-args (echo This is a test)
 *
 * What this phase implements:
 *   - Tree-sitter parse → AST walk via run_node() dispatcher
 *   - expand_node()     — plain words only (Phase 1 baseline)
 *   - build_argv()      — builds NULL-terminated argv from command node
 *   - try_builtin()     — handles "exit" and "cd"
 *   - run_simple_command() — spawns external commands with posix_spawnp
 *   - Proper job management: allocate_job / wait_for_job / delete_job
 *   - SIGCHLD handler + handle_child_status
 *   - find_job_by_pid via process group (pgid)
 *   - Passes `environ` so children inherit the environment
 *   - Sets POSIX_SPAWN_SETPGROUP so each job gets its own group
 *
 * Design decisions:
 *   - run_node() is the single dispatcher (replaces the old run_program
 *     switch).  Every later phase just adds cases here.
 *   - run_program() iterates top-level statements and calls run_node().
 *   - last_exit_status tracks $? globally (used starting Phase 2).
 *   - No debug printf statements.
 */
#define _GNU_SOURCE 1
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
#pragma GCC diagnostic ignored "-Wunused-function"

#include "hashtable.h"
#include "signal_support.h"
#include "utils.h"
#include "list.h"
#include "ts_helpers.h"

extern char **environ;

/* =========================================================================
 * Global state
 * ========================================================================= */

static TSFieldId bodyId, redirectId, destinationId, valueId, nameId, conditionId;
static TSFieldId variableId;
static TSFieldId leftId, operatorId, rightId, descriptorId;

static char *input;
static TSParser *parser;
static tommy_hashdyn shell_vars;
static int last_exit_status = 0;

/* =========================================================================
 * Job data structures
 *
 * Each spawned process (or pipeline) is tracked as a "job."
 * Jobs live in two data structures:
 *   (a) jid2job[] — O(1) lookup by job id
 *   (b) job_list  — linked list for iteration
 * ========================================================================= */

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

/* Allocate a new job, optionally adding it to the job list. */
static struct job *
allocate_job(bool includeinjoblist)
{
    struct job *job = malloc(sizeof *job);
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

/* Delete a job.  Only call when all processes are known dead. */
static void
delete_job(struct job *job, bool removeFromJobList)
{
    if (removeFromJobList) {
        int jid = job->jid;
        assert(jid != -1);
        assert(jid2job[jid] == job);
        list_remove(&job->elem);
        jid2job[jid] = NULL;
    } else {
        assert(job->jid == -1);
    }
    free(job);
}

/* =========================================================================
 * SIGCHLD / wait_for_job / handle_child_status
 *
 * find_job_by_pid: iterates the job list, uses getpgid() to map
 *   any child pid back to its process group leader (stored in job->pgid).
 *
 * handle_child_status: translates waitpid status into job state.
 *   Crucially, only marks the job as TERMINATED when
 *   num_processes_alive reaches 0 (important for pipelines later).
 *
 * wait_for_job: busy-waits (with SIGCHLD blocked) until the job
 *   leaves FOREGROUND state or has no alive processes.
 * ========================================================================= */

static void handle_child_status(pid_t pid, int status);

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

static struct job *
find_job_by_pid(pid_t pid)
{
    struct list_elem *e;
    for (e = list_begin(&job_list); e != list_end(&job_list); e = list_next(e)) {
        struct job *j = list_entry(e, struct job, elem);
        /* For single-process jobs, pgid == child pid */
        if (j->pgid == pid)
            return j;
        /* For pipeline children, check their process group */
        pid_t pg = getpgid(pid);
        if (pg != -1 && pg == j->pgid)
            return j;
    }
    return NULL;
}

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
 *
 * Takes a tree-sitter node and returns the string it represents
 * at runtime.  In Phase 1 we only handle plain "word" nodes
 * by copying the raw source text.
 *
 * The command_name node wraps the actual word in a named child,
 * so we recurse into it.
 *
 * Everything else falls through to raw-text extraction as a safe
 * default (so the shell doesn't crash on unimplemented node types).
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

    /* Fallback: raw source text */
    return ts_extract_node_text(input, node);
}

/* =========================================================================
 * build_argv / free_argv
 *
 * Walk the named children of a "command" node and build a
 * NULL-terminated argv array suitable for posix_spawnp().
 *
 * Skips file_redirect children (they are handled separately).
 * Uses a dynamically growing array so any number of args works.
 * ========================================================================= */

static char **
build_argv(TSNode cmd_node)
{
    int capacity = 8, argc = 0;
    char **argv = malloc(capacity * sizeof(char *));

    uint32_t nc = ts_node_named_child_count(cmd_node);
    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_named_child(cmd_node, i);
        const char *ctype = ts_node_type(child);

        if (strcmp(ctype, "file_redirect") == 0)
            continue;

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
 * Returns true if the command was a builtin (and we handled it).
 * Sets last_exit_status.
 * ========================================================================= */

static bool
try_builtin(char **argv)
{
    if (argv[0] == NULL) return false;

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

/* =========================================================================
 * run_simple_command
 *
 * 1. Build argv from the command node
 * 2. Check builtins first
 * 3. Set up posix_spawn attributes:
 *    - POSIX_SPAWN_SETPGROUP with pgid=0 → child gets its own group
 * 4. Spawn the child via posix_spawnp (searches PATH)
 * 5. Allocate a FOREGROUND job, record pgid = child pid
 * 6. wait_for_job() → blocks until child exits
 * 7. Record last_exit_status, delete the job
 * ========================================================================= */

static int
run_simple_command(TSNode node)
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

    posix_spawn_file_actions_t fa;
    posix_spawnattr_t attr;
    posix_spawn_file_actions_init(&fa);
    posix_spawnattr_init(&attr);

    posix_spawnattr_setpgroup(&attr, 0);
    int flags = POSIX_SPAWN_SETPGROUP;
#ifdef POSIX_SPAWN_USEVFORK
    flags |= POSIX_SPAWN_USEVFORK;
#endif
    posix_spawnattr_setflags(&attr, flags);

    pid_t child;
    int rc = posix_spawnp(&child, argv[0], &fa, &attr, argv, environ);
    posix_spawn_file_actions_destroy(&fa);
    posix_spawnattr_destroy(&attr);
    free_argv(argv);

    if (rc != 0) {
        fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(rc));
        last_exit_status = 127;
        return 127;
    }

    struct job *job = allocate_job(true);
    job->status = FOREGROUND;
    job->pgid = child;
    job->num_processes_alive = 1;

    wait_for_job(job);
    last_exit_status = job->exit_status;
    delete_job(job, true);

    return last_exit_status;
}

/* =========================================================================
 * run_node — the central dispatcher
 *
 * Phase 1 handles:
 *   "comment"  → skip (return 0)
 *   "command"  → run_simple_command()
 *
 * Everything else prints "not yet implemented."
 * ========================================================================= */

static int
run_node(TSNode node, bool background)
{
    if (ts_node_is_null(node)) return 0;
    const char *type = ts_node_type(node);

    if (strcmp(type, "comment") == 0) return 0;
    if (strcmp(type, "command") == 0) return run_simple_command(node);

    fprintf(stderr, "minibash: node type '%s' not yet implemented\n", type);
    return 0;
}

/* =========================================================================
 * run_program — iterate top-level statements
 * ========================================================================= */

static void
run_program(TSNode program)
{
    uint32_t n = ts_node_named_child_count(program);
    for (uint32_t i = 0; i < n; i++)
        run_node(ts_node_named_child(program, i), false);
}

/* =========================================================================
 * Script reading / execution / main
 * ========================================================================= */

static char *
read_script_from_fd(int readfd)
{
    struct stat st;
    if (fstat(readfd, &st) != 0) { utils_error("fstat"); return NULL; }
    char *buf = malloc(st.st_size + 1);
    if (read(readfd, buf, st.st_size) != st.st_size) { utils_error("read"); free(buf); return NULL; }
    buf[st.st_size] = 0;
    return buf;
}

static void
execute_script(char *script)
{
    input = script;
    TSTree *tree = ts_parser_parse_string(parser, NULL, input, strlen(input));
    TSNode program = ts_tree_root_node(tree);
    signal_block(SIGCHLD);
    run_program(program);
    signal_unblock(SIGCHLD);
    ts_tree_delete(tree);
}

static void usage(char *p) { printf("Usage: %s -h\n", p); exit(EXIT_SUCCESS); }
static char *build_prompt(void) { return strdup("minibash> "); }

int
main(int ac, char *av[])
{
    int opt;
    tommy_hashdyn_init(&shell_vars);
    while ((opt = getopt(ac, av, "h")) > 0)
        if (opt == 'h') usage(av[0]);

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
    DEFINE_FIELD_ID(descriptor);
    ts_parser_set_language(parser, bash);

    list_init(&job_list);
    signal_set_handler(SIGCHLD, sigchld_handler);

    bool shouldexit = false;
    for (;;) {
        if (shouldexit) break;
        assert(!signal_is_blocked(SIGCHLD));
        char *userinput = NULL;
        if (isatty(0) && av[optind] == NULL) {
            char *prompt = build_prompt();
            userinput = readline(prompt);
            free(prompt);
            if (userinput == NULL) break;
        } else {
            int readfd = av[optind] ? open(av[optind], O_RDONLY) : 0;
            userinput = read_script_from_fd(readfd);
            if (av[optind] != NULL) close(readfd);
            if (userinput == NULL) utils_fatal_error("Could not read input");
            shouldexit = true;
        }
        execute_script(userinput);
        free(userinput);
    }

    ts_parser_delete(parser);
    tommy_hashdyn_foreach(&shell_vars, hash_free);
    tommy_hashdyn_done(&shell_vars);
    return last_exit_status;
}
