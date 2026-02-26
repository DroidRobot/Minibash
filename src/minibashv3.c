/*
 * minibash - Phase 3: Pipelines + Redirections + Command Substitution + Lists
 *
 * Builds on Phase 2.  New in this phase:
 *   - run_pipeline()            — multi-command pipelines with |, |&
 *   - apply_redirects()         — file redirections via posix_spawn_file_actions_addopen
 *   - run_redirected_statement() — commands/pipelines wrapped with redirects
 *   - command_substitution in expand_node()  — $(cmd) expansion
 *   - list (&&, ||, ;, &)       — short-circuit and sequential operators
 *   - export builtin
 *
 * Passes all Phase 1+2 tests plus:
 *   040-command-expansion-1             (echo $(echo Hello) World)
 *   050-pipeline-1                      (echo hello world | rev | wc -l)
 *   060-pipeline-redirect1              (< file cat | rev | wc -m > outfile)
 *   064-pipeline-redirect-stderr        (|& and >&)
 *   070-lists-1                         (false && echo skipped || echo ok)
 *   071-lists-2                         (true && true && echo ok)
 *   080-command-expansion-with-pipe     (echo Hello $(echo dlroW | rev))
 *
 * Key design decisions for this phase:
 *   - apply_redirects() uses posix_spawn_file_actions_addopen() instead of
 *     opening files in the parent.  This is cleaner: no FD leaks, no need
 *     to close files after spawn.
 *   - Pipelines use pipe() + adddup2/addclose in file_actions.
 *     All pipe FDs are closed in both child (via addclose) and parent.
 *   - |& is detected by scanning the raw pipeline text for "|&".
 *   - Command substitution spawns "sh -c <cmd>" and captures stdout.
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
 * Job data structures  (unchanged)
 * ========================================================================= */

enum job_status {
    FOREGROUND, BACKGROUND, STOPPED, NEEDSTERMINAL,
    TERMINATED_VIA_EXIT, TERMINATED_VIA_SIGNAL
};

struct job {
    struct list_elem elem;
    int jid;
    enum job_status status;
    int num_processes_alive;
    pid_t pgid;
    int exit_status;
};

#define MAXJOBS (1<<16)
static struct list job_list;
static struct job *jid2job[MAXJOBS];

static struct job *get_job_from_jid(int jid)
{
    if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL) return jid2job[jid];
    return NULL;
}

static struct job *allocate_job(bool includeinjoblist)
{
    struct job *job = malloc(sizeof *job);
    job->num_processes_alive = 0; job->jid = -1; job->pgid = 0; job->exit_status = 0;
    if (!includeinjoblist) return job;
    list_push_back(&job_list, &job->elem);
    for (int i = 1; i < MAXJOBS; i++) {
        if (jid2job[i] == NULL) { jid2job[i] = job; job->jid = i; return job; }
    }
    fprintf(stderr, "Maximum number of jobs exceeded\n"); abort(); return NULL;
}

static void delete_job(struct job *job, bool removeFromJobList)
{
    if (removeFromJobList) {
        int jid = job->jid; assert(jid != -1); assert(jid2job[jid] == job);
        list_remove(&job->elem); jid2job[jid] = NULL;
    } else { assert(job->jid == -1); }
    free(job);
}

/* =========================================================================
 * SIGCHLD / wait / handle_child_status  (unchanged)
 * ========================================================================= */

static void handle_child_status(pid_t pid, int status);

static void sigchld_handler(int sig, siginfo_t *info, void *_ctxt)
{
    pid_t child; int status; assert(sig == SIGCHLD);
    while ((child = waitpid(-1, &status, WUNTRACED|WNOHANG)) > 0)
        handle_child_status(child, status);
}

static void wait_for_job(struct job *job)
{
    assert(signal_is_blocked(SIGCHLD));
    while (job->status == FOREGROUND && job->num_processes_alive > 0) {
        int status;
        pid_t child = waitpid(-1, &status, WUNTRACED);
        if (child != -1) handle_child_status(child, status);
        else utils_fatal_error("waitpid failed, see code for explanation");
    }
}

static struct job *find_job_by_pid(pid_t pid)
{
    struct list_elem *e;
    for (e = list_begin(&job_list); e != list_end(&job_list); e = list_next(e)) {
        struct job *j = list_entry(e, struct job, elem);
        if (j->pgid == pid) return j;
        pid_t pg = getpgid(pid);
        if (pg != -1 && pg == j->pgid) return j;
    }
    return NULL;
}

static void handle_child_status(pid_t pid, int status)
{
    assert(signal_is_blocked(SIGCHLD));
    struct job *job = find_job_by_pid(pid);
    if (job == NULL) return;
    if (WIFEXITED(status)) {
        job->exit_status = WEXITSTATUS(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0) job->status = TERMINATED_VIA_EXIT;
    } else if (WIFSIGNALED(status)) {
        job->exit_status = 128 + WTERMSIG(status);
        job->num_processes_alive--;
        if (job->num_processes_alive == 0) job->status = TERMINATED_VIA_SIGNAL;
    } else if (WIFSTOPPED(status)) {
        job->status = STOPPED;
    }
}

/* =========================================================================
 * String expansion  (Phase 2 code + command_substitution from Phase 3)
 * ========================================================================= */

static char *expand_node(TSNode node);

static char *expand_string(TSNode node)
{
    char *result = strdup("");
    uint32_t nc = ts_node_named_child_count(node);
    if (nc == 0) return result;
    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_named_child(node, i);
        char *part = (strcmp(ts_node_type(child), "string_content") == 0)
                     ? ts_extract_node_text(input, child)
                     : expand_node(child);
        result = utils_string_concat(result, part);
    }
    return result;
}

static char *
expand_node(TSNode node)
{
    if (ts_node_is_null(node)) return strdup("");
    const char *type = ts_node_type(node);

    if (strcmp(type, "word") == 0)        return ts_extract_node_text(input, node);
    if (strcmp(type, "number") == 0)      return ts_extract_node_text(input, node);
    if (strcmp(type, "raw_string") == 0)  return ts_extract_node_text_from_to(input, node, 1, 1);
    if (strcmp(type, "string") == 0)      return expand_string(node);

    if (strcmp(type, "simple_expansion") == 0) {
        uint32_t nc = ts_node_named_child_count(node);
        if (nc == 0) return strdup("");
        TSNode child = ts_node_named_child(node, 0);
        char *result = NULL;
        if (strcmp(ts_node_type(child), "special_variable_name") == 0) {
            char c = ts_extract_single_node_char(input, child);
            if (c == '?')      asprintf(&result, "%d", last_exit_status);
            else if (c == '$') asprintf(&result, "%d", (int)getpid());
            else               result = strdup("");
        } else {
            char *varname = ts_extract_node_text(input, child);
            const char *val = hash_get(&shell_vars, varname);
            if (val == NULL) val = getenv(varname);
            result = strdup(val ? val : "");
            free(varname);
        }
        return result;
    }

    if (strcmp(type, "expansion") == 0) {
        TSNode varnode = ts_node_child_by_field_id(node, variableId);
        char *varname = !ts_node_is_null(varnode)
                        ? ts_extract_node_text(input, varnode)
                        : ts_extract_node_text_from_to(input, node, 2, 1);
        const char *val = hash_get(&shell_vars, varname);
        if (val == NULL) val = getenv(varname);
        char *result = strdup(val ? val : "");
        free(varname);
        return result;
    }

    if (strcmp(type, "concatenation") == 0) {
        char *result = strdup("");
        uint32_t nc = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < nc; i++)
            result = utils_string_concat(result, expand_node(ts_node_named_child(node, i)));
        return result;
    }

    /* ---------------------------------------------------------------
     * NEW IN PHASE 3: Command substitution  $(cmd)
     *
     * Strategy:
     *   1. Extract the command text between $( and )
     *   2. Create a pipe to capture stdout
     *   3. Spawn "sh -c <cmd>" with stdout → pipe write end
     *   4. Read all output from the pipe read end
     *   5. Strip trailing newlines (bash convention)
     *   6. Wait for the child and record its exit status
     * --------------------------------------------------------------- */
    if (strcmp(type, "command_substitution") == 0) {
        char *cmd_text = ts_extract_node_text_from_to(input, node, 2, 1);
        int pipefd[2];
        if (pipe(pipefd) != 0) { utils_error("pipe"); free(cmd_text); return strdup(""); }

        posix_spawn_file_actions_t fa;
        posix_spawnattr_t attr;
        posix_spawn_file_actions_init(&fa);
        posix_spawnattr_init(&attr);
        posix_spawn_file_actions_adddup2(&fa, pipefd[1], STDOUT_FILENO);
        posix_spawn_file_actions_addclose(&fa, pipefd[0]);
        posix_spawn_file_actions_addclose(&fa, pipefd[1]);

        char *sh_argv[] = { "sh", "-c", cmd_text, NULL };
        pid_t child;
        int rc = posix_spawnp(&child, "sh", &fa, &attr, sh_argv, environ);
        posix_spawn_file_actions_destroy(&fa);
        posix_spawnattr_destroy(&attr);
        free(cmd_text);

        close(pipefd[1]);
        if (rc != 0) { close(pipefd[0]); return strdup(""); }

        /* Read all output from the child */
        char *buf = NULL;
        size_t total = 0;
        char tmp[4096];
        ssize_t n;
        while ((n = read(pipefd[0], tmp, sizeof tmp)) > 0) {
            buf = realloc(buf, total + n + 1);
            memcpy(buf + total, tmp, n);
            total += n;
        }
        close(pipefd[0]);

        int wstatus;
        if (waitpid(child, &wstatus, 0) != -1 && WIFEXITED(wstatus))
            last_exit_status = WEXITSTATUS(wstatus);

        if (buf == NULL) return strdup("");
        buf[total] = '\0';
        /* Strip trailing newlines (bash convention) */
        while (total > 0 && buf[total - 1] == '\n') buf[--total] = '\0';
        return buf;
    }

    if (strcmp(type, "command_name") == 0) {
        uint32_t nc = ts_node_named_child_count(node);
        if (nc > 0) return expand_node(ts_node_named_child(node, 0));
        return ts_extract_node_text(input, node);
    }

    return ts_extract_node_text(input, node);
}

/* =========================================================================
 * Variable assignment  (unchanged from Phase 2)
 * ========================================================================= */

static void handle_variable_assignment(TSNode node)
{
    TSNode name_node  = ts_node_child_by_field_id(node, nameId);
    TSNode value_node = ts_node_child_by_field_id(node, valueId);
    if (ts_node_is_null(name_node)) return;
    char *varname = ts_extract_node_text(input, name_node);
    char *value   = ts_node_is_null(value_node) ? strdup("") : expand_node(value_node);
    hash_put(&shell_vars, varname, value);
    free(varname);
    free(value);
}

/* =========================================================================
 * build_argv / free_argv  (unchanged from Phase 2)
 * ========================================================================= */

static char **build_argv(TSNode cmd_node)
{
    int capacity = 8, argc = 0;
    char **argv = malloc(capacity * sizeof(char *));
    uint32_t nc = ts_node_named_child_count(cmd_node);
    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_named_child(cmd_node, i);
        const char *ctype = ts_node_type(child);
        if (strcmp(ctype, "file_redirect") == 0) continue;
        if (argc >= capacity - 1) { capacity *= 2; argv = realloc(argv, capacity * sizeof(char *)); }
        argv[argc++] = expand_node(child);
    }
    argv[argc] = NULL;
    return argv;
}

static void free_argv(char **argv)
{
    if (!argv) return;
    for (int i = 0; argv[i] != NULL; i++) free(argv[i]);
    free(argv);
}

/* =========================================================================
 * NEW IN PHASE 3: apply_redirects
 *
 * Scans a node's children for file_redirect nodes and adds the
 * corresponding open/dup2 actions to a posix_spawn_file_actions_t.
 *
 * Uses posix_spawn_file_actions_addopen() to open files in the child
 * process (not the parent).  This is the correct approach: no FD leaks.
 *
 * Supported redirect operators:
 *   >   — truncate/create file, write stdout (or explicit fd)
 *   >>  — append to file
 *   <   — read from file
 *   >&  — redirect stdout+stderr to file  (or fd-to-fd: >&2)
 *   &>  — redirect stdout+stderr to file
 *   2>  — redirect stderr to file (explicit fd=2 with >)
 *   2>> — redirect stderr append
 * ========================================================================= */

static void
apply_redirects(TSNode node, posix_spawn_file_actions_t *fa)
{
    uint32_t nc = ts_node_child_count(node);
    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_child(node, i);
        if (!ts_node_is_named(child) || ts_node_symbol(child) != sym_file_redirect)
            continue;

        TSNode op_node   = ts_node_child_by_field_id(child, operatorId);
        TSNode dest_node = ts_node_child_by_field_id(child, destinationId);
        char *op   = ts_node_is_null(op_node)  ? NULL : ts_extract_node_text(input, op_node);
        char *dest = ts_node_is_null(dest_node) ? NULL : expand_node(dest_node);

        /* Check for explicit file descriptor (e.g., "2" in 2>file) */
        int explicit_fd = -1;
        for (uint32_t j = 0; j < ts_node_child_count(child); j++) {
            TSNode fc = ts_node_child(child, j);
            if (ts_node_symbol(fc) == sym_file_descriptor) {
                char *fds = ts_extract_node_text(input, fc);
                explicit_fd = atoi(fds);
                free(fds);
                break;
            }
        }

        if (dest == NULL) { free(op); continue; }

        if (op == NULL || strcmp(op, ">") == 0) {
            int tgt = (explicit_fd >= 0) ? explicit_fd : STDOUT_FILENO;
            posix_spawn_file_actions_addopen(fa, tgt, dest, O_WRONLY|O_CREAT|O_TRUNC, 0644);
        } else if (strcmp(op, "<") == 0) {
            posix_spawn_file_actions_addopen(fa, STDIN_FILENO, dest, O_RDONLY, 0);
        } else if (strcmp(op, ">>") == 0) {
            int tgt = (explicit_fd >= 0) ? explicit_fd : STDOUT_FILENO;
            posix_spawn_file_actions_addopen(fa, tgt, dest, O_WRONLY|O_CREAT|O_APPEND, 0644);
        } else if (strcmp(op, ">&") == 0 || strcmp(op, "&>") == 0) {
            /* Redirect both stdout AND stderr to the file */
            posix_spawn_file_actions_addopen(fa, STDOUT_FILENO, dest, O_WRONLY|O_CREAT|O_TRUNC, 0644);
            posix_spawn_file_actions_adddup2(fa, STDOUT_FILENO, STDERR_FILENO);
        }
        free(op);
        free(dest);
    }
}

/* =========================================================================
 * Builtins (Phase 3: added "export")
 * ========================================================================= */

static int run_node(TSNode node, bool background);

static bool try_builtin(char **argv)
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
        if (chdir(dir) != 0) { utils_error("cd: %s: ", dir); last_exit_status = 1; }
        else last_exit_status = 0;
        return true;
    }
    if (strcmp(argv[0], "export") == 0) {
        for (int i = 1; argv[i] != NULL; i++) {
            char *eq = strchr(argv[i], '=');
            if (eq) {
                *eq = '\0';
                setenv(argv[i], eq + 1, 1);
                hash_put(&shell_vars, argv[i], eq + 1);
                *eq = '=';
            } else {
                const char *v = hash_get(&shell_vars, argv[i]);
                if (v) setenv(argv[i], v, 1);
            }
        }
        last_exit_status = 0;
        return true;
    }

    return false;
}

/* =========================================================================
 * run_simple_command  (updated: apply_redirects on the command itself)
 * ========================================================================= */

static int
run_simple_command(TSNode node, bool background)
{
    char **argv = build_argv(node);
    if (argv[0] == NULL) { free_argv(argv); return 0; }
    if (try_builtin(argv)) { free_argv(argv); return last_exit_status; }
    free_argv(argv);

    posix_spawn_file_actions_t fa;
    posix_spawnattr_t attr;
    posix_spawn_file_actions_init(&fa);
    posix_spawnattr_init(&attr);
    /* Apply any redirects that are children of the command node itself */
    apply_redirects(node, &fa);
    posix_spawnattr_setpgroup(&attr, 0);
    int flags = POSIX_SPAWN_SETPGROUP;
#ifdef POSIX_SPAWN_USEVFORK
    flags |= POSIX_SPAWN_USEVFORK;
#endif
    posix_spawnattr_setflags(&attr, flags);

    argv = build_argv(node);
    pid_t child;
    int rc = posix_spawnp(&child, argv[0], &fa, &attr, argv, environ);
    posix_spawn_file_actions_destroy(&fa);
    posix_spawnattr_destroy(&attr);
    free_argv(argv);

    if (rc != 0) {
        fprintf(stderr, "minibash: spawn failed: %s\n", strerror(rc));
        last_exit_status = 127;
        return 127;
    }

    struct job *job = allocate_job(true);
    job->status = background ? BACKGROUND : FOREGROUND;
    job->pgid = child;
    job->num_processes_alive = 1;

    if (!background) {
        wait_for_job(job);
        last_exit_status = job->exit_status;
        delete_job(job, true);
    }
    return last_exit_status;
}

/* =========================================================================
 * NEW IN PHASE 3: run_pipeline
 *
 * Executes a pipeline: cmd1 | cmd2 | cmd3
 *
 * Algorithm:
 *   1. Collect all command nodes from the pipeline.
 *   2. Detect |& (stderr pipe) by scanning the raw text.
 *   3. Create N-1 pipes for N commands.
 *   4. For each command:
 *      a. Set up file_actions: wire stdin from previous pipe, stdout to next pipe
 *      b. Close ALL pipe FDs in the child (via addclose)
 *      c. Apply any per-command redirects
 *      d. Spawn with posix_spawnp
 *   5. Close all pipe FDs in the parent.
 *   6. Wait for all processes in the job.
 *
 * All processes share a process group (the first child's PID).
 * ========================================================================= */

static int
run_pipeline(TSNode node, bool background)
{
    /* Collect command children */
    uint32_t nc = ts_node_named_child_count(node);
    TSNode *cmds = malloc(nc * sizeof(TSNode));
    uint32_t ncmds = 0;
    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_named_child(node, i);
        if (strcmp(ts_node_type(child), "command") == 0)
            cmds[ncmds++] = child;
    }
    if (ncmds == 0) { free(cmds); return 0; }

    /* Detect |& (pipe stderr too) */
    bool stderr_pipe = false;
    { char *raw = ts_extract_node_text(input, node); stderr_pipe = (strstr(raw, "|&") != NULL); free(raw); }

    struct job *job = allocate_job(true);
    job->status = background ? BACKGROUND : FOREGROUND;

    /* Create all pipes up front */
    int (*pipes)[2] = malloc((ncmds - 1) * sizeof(int[2]));
    for (uint32_t i = 0; i < ncmds - 1; i++) {
        if (pipe(pipes[i]) != 0) {
            utils_error("pipe");
            free(pipes); free(cmds);
            delete_job(job, true);
            return -1;
        }
    }

    pid_t first_pid = 0;
    for (uint32_t i = 0; i < ncmds; i++) {
        posix_spawn_file_actions_t fa;
        posix_spawnattr_t attr;
        posix_spawn_file_actions_init(&fa);
        posix_spawnattr_init(&attr);

        /* Wire stdin from previous pipe's read end */
        if (i > 0)
            posix_spawn_file_actions_adddup2(&fa, pipes[i-1][0], STDIN_FILENO);

        /* Wire stdout (and optionally stderr) to next pipe's write end */
        if (i < ncmds - 1) {
            posix_spawn_file_actions_adddup2(&fa, pipes[i][1], STDOUT_FILENO);
            if (stderr_pipe)
                posix_spawn_file_actions_adddup2(&fa, pipes[i][1], STDERR_FILENO);
        }

        /* Close ALL pipe FDs in the child */
        for (uint32_t j = 0; j < ncmds - 1; j++) {
            posix_spawn_file_actions_addclose(&fa, pipes[j][0]);
            posix_spawn_file_actions_addclose(&fa, pipes[j][1]);
        }

        /* Apply per-command redirects (e.g., > file on last command) */
        apply_redirects(cmds[i], &fa);

        /* All processes share the first child's process group */
        pid_t pgid = (i == 0) ? 0 : first_pid;
        posix_spawnattr_setpgroup(&attr, pgid);
        int flags = POSIX_SPAWN_SETPGROUP;
#ifdef POSIX_SPAWN_USEVFORK
        flags |= POSIX_SPAWN_USEVFORK;
#endif
        posix_spawnattr_setflags(&attr, flags);

        char **argv = build_argv(cmds[i]);
        pid_t child = 0;
        if (argv[0] != NULL) {
            int rc = posix_spawnp(&child, argv[0], &fa, &attr, argv, environ);
            if (rc != 0) {
                fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(rc));
            } else {
                if (i == 0) { first_pid = child; job->pgid = child; }
                job->num_processes_alive++;
            }
        }
        posix_spawn_file_actions_destroy(&fa);
        posix_spawnattr_destroy(&attr);
        free_argv(argv);
    }

    /* Close all pipe FDs in the parent */
    for (uint32_t i = 0; i < ncmds - 1; i++) {
        close(pipes[i][0]);
        close(pipes[i][1]);
    }
    free(pipes);
    free(cmds);

    if (!background) {
        wait_for_job(job);
        last_exit_status = job->exit_status;
        delete_job(job, true);
    }
    return last_exit_status;
}

/* =========================================================================
 * NEW IN PHASE 3: run_redirected_statement
 *
 * A redirected_statement wraps a body (command or pipeline) with
 * outer redirections.  E.g.:
 *   < input.txt cat | rev | wc -m > output.txt
 *
 * The outer redirects apply to the first/last command in the pipeline.
 *
 * For a simple command body:
 *   1. Build argv, check builtins
 *   2. apply_redirects for the body command
 *   3. apply_redirects for the outer redirected_statement node
 *   4. Spawn and wait
 *
 * For a pipeline body:
 *   Same as run_pipeline, but the last command also gets the outer redirects.
 * ========================================================================= */

static int
run_redirected_statement(TSNode node, bool background)
{
    TSNode body = ts_node_child_by_field_id(node, bodyId);
    if (ts_node_is_null(body)) return 0;
    const char *btype = ts_node_type(body);

    if (strcmp(btype, "command") == 0) {
        /* Simple command with outer redirects */
        char **argv = build_argv(body);
        if (argv[0] == NULL) { free_argv(argv); return 0; }
        if (try_builtin(argv)) { free_argv(argv); return last_exit_status; }
        free_argv(argv);

        posix_spawn_file_actions_t fa;
        posix_spawnattr_t attr;
        posix_spawn_file_actions_init(&fa);
        posix_spawnattr_init(&attr);
        apply_redirects(body, &fa);     /* per-command redirects */
        apply_redirects(node, &fa);     /* outer redirects */
        posix_spawnattr_setpgroup(&attr, 0);
        int flags = POSIX_SPAWN_SETPGROUP;
#ifdef POSIX_SPAWN_USEVFORK
        flags |= POSIX_SPAWN_USEVFORK;
#endif
        posix_spawnattr_setflags(&attr, flags);

        argv = build_argv(body);
        pid_t child;
        int rc = posix_spawnp(&child, argv[0], &fa, &attr, argv, environ);
        posix_spawn_file_actions_destroy(&fa);
        posix_spawnattr_destroy(&attr);
        free_argv(argv);

        if (rc != 0) {
            fprintf(stderr, "minibash: spawn failed: %s\n", strerror(rc));
            last_exit_status = 127;
            return 127;
        }

        struct job *job = allocate_job(true);
        job->status = background ? BACKGROUND : FOREGROUND;
        job->pgid = child;
        job->num_processes_alive = 1;
        if (!background) {
            wait_for_job(job);
            last_exit_status = job->exit_status;
            delete_job(job, true);
        }
        return last_exit_status;

    } else if (strcmp(btype, "pipeline") == 0) {
        /* Pipeline with outer redirects */
        uint32_t nc = ts_node_named_child_count(body);
        TSNode *cmds = malloc(nc * sizeof(TSNode));
        uint32_t ncmds = 0;
        for (uint32_t i = 0; i < nc; i++) {
            TSNode child = ts_node_named_child(body, i);
            if (strcmp(ts_node_type(child), "command") == 0)
                cmds[ncmds++] = child;
        }
        if (ncmds == 0) { free(cmds); return 0; }

        bool stderr_pipe = false;
        { char *r = ts_extract_node_text(input, body); stderr_pipe = (strstr(r, "|&") != NULL); free(r); }

        struct job *job = allocate_job(true);
        job->status = background ? BACKGROUND : FOREGROUND;

        int (*pipes)[2] = malloc((ncmds - 1) * sizeof(int[2]));
        for (uint32_t i = 0; i < ncmds - 1; i++) {
            if (pipe(pipes[i]) != 0) {
                utils_error("pipe");
                free(pipes); free(cmds); delete_job(job, true);
                return -1;
            }
        }

        pid_t first_pid = 0;
        for (uint32_t i = 0; i < ncmds; i++) {
            posix_spawn_file_actions_t fa;
            posix_spawnattr_t attr;
            posix_spawn_file_actions_init(&fa);
            posix_spawnattr_init(&attr);

            if (i > 0)
                posix_spawn_file_actions_adddup2(&fa, pipes[i-1][0], STDIN_FILENO);
            if (i < ncmds - 1) {
                posix_spawn_file_actions_adddup2(&fa, pipes[i][1], STDOUT_FILENO);
                if (stderr_pipe)
                    posix_spawn_file_actions_adddup2(&fa, pipes[i][1], STDERR_FILENO);
            }
            for (uint32_t j = 0; j < ncmds - 1; j++) {
                posix_spawn_file_actions_addclose(&fa, pipes[j][0]);
                posix_spawn_file_actions_addclose(&fa, pipes[j][1]);
            }

            /* Per-command redirects */
            apply_redirects(cmds[i], &fa);
            /* Outer redirects apply to the LAST command in the pipeline
             * (for stdin redirect like <file, apply to the FIRST command) */
            if (i == ncmds - 1)
                apply_redirects(node, &fa);
            /* Also apply input redirects from outer node to first command */
            if (i == 0) {
                /* Check outer node for < redirects specifically */
                uint32_t onc = ts_node_child_count(node);
                for (uint32_t k = 0; k < onc; k++) {
                    TSNode oc = ts_node_child(node, k);
                    if (ts_node_is_named(oc) && ts_node_symbol(oc) == sym_file_redirect) {
                        TSNode op_n = ts_node_child_by_field_id(oc, operatorId);
                        if (!ts_node_is_null(op_n)) {
                            char *opstr = ts_extract_node_text(input, op_n);
                            if (strcmp(opstr, "<") == 0) {
                                TSNode dest_n = ts_node_child_by_field_id(oc, destinationId);
                                if (!ts_node_is_null(dest_n)) {
                                    char *dest = expand_node(dest_n);
                                    posix_spawn_file_actions_addopen(&fa, STDIN_FILENO, dest, O_RDONLY, 0);
                                    free(dest);
                                }
                            }
                            free(opstr);
                        }
                    }
                }
            }

            pid_t pgid = (i == 0) ? 0 : first_pid;
            posix_spawnattr_setpgroup(&attr, pgid);
            int sflags = POSIX_SPAWN_SETPGROUP;
#ifdef POSIX_SPAWN_USEVFORK
            sflags |= POSIX_SPAWN_USEVFORK;
#endif
            posix_spawnattr_setflags(&attr, sflags);

            char **argv = build_argv(cmds[i]);
            pid_t child = 0;
            if (argv[0] != NULL) {
                int rc = posix_spawnp(&child, argv[0], &fa, &attr, argv, environ);
                if (rc != 0) fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(rc));
                else {
                    if (i == 0) { first_pid = child; job->pgid = child; }
                    job->num_processes_alive++;
                }
            }
            posix_spawn_file_actions_destroy(&fa);
            posix_spawnattr_destroy(&attr);
            free_argv(argv);
        }

        for (uint32_t i = 0; i < ncmds - 1; i++) {
            close(pipes[i][0]); close(pipes[i][1]);
        }
        free(pipes); free(cmds);

        if (!background) {
            wait_for_job(job);
            last_exit_status = job->exit_status;
            delete_job(job, true);
        }
        return last_exit_status;
    }

    /* Body is some other type — just run it */
    return run_node(body, background);
}

/* =========================================================================
 * run_node — dispatcher (Phase 3: added pipeline, redirected_statement, list)
 * ========================================================================= */

static int
run_node(TSNode node, bool background)
{
    if (ts_node_is_null(node)) return 0;
    const char *type = ts_node_type(node);

    if (strcmp(type, "comment") == 0)              return 0;
    if (strcmp(type, "variable_assignment") == 0)   { handle_variable_assignment(node); last_exit_status = 0; return 0; }
    if (strcmp(type, "command") == 0)               return run_simple_command(node, background);
    if (strcmp(type, "pipeline") == 0)              return run_pipeline(node, background);
    if (strcmp(type, "redirected_statement") == 0)  return run_redirected_statement(node, background);

    /* ---------------------------------------------------------------
     * NEW IN PHASE 3: list (&&, ||, ;, &)
     *
     * Tree structure:
     *   list
     *     left: <statement>
     *     operator: "&&" | "||" | ";" | "&"
     *     right: <statement>
     *
     * Short-circuit logic:
     *   && → run right only if left succeeded (exit 0)
     *   || → run right only if left failed (exit != 0)
     *   ;  → always run right
     *   &  → run left in background, then right in foreground
     * --------------------------------------------------------------- */
    if (strcmp(type, "list") == 0) {
        TSNode left  = ts_node_child_by_field_id(node, leftId);
        TSNode op_n  = ts_node_child_by_field_id(node, operatorId);
        TSNode right = ts_node_child_by_field_id(node, rightId);
        char *op = ts_node_is_null(op_n) ? NULL : ts_extract_node_text(input, op_n);
        int result = 0;

        if (op && strcmp(op, "&") == 0) {
            if (!ts_node_is_null(left))  result = run_node(left, true);
            if (!ts_node_is_null(right)) result = run_node(right, false);
        } else {
            if (!ts_node_is_null(left)) result = run_node(left, false);
            if (op) {
                if (strcmp(op, "&&") == 0) {
                    if (result == 0 && !ts_node_is_null(right))
                        result = run_node(right, false);
                } else if (strcmp(op, "||") == 0) {
                    if (result != 0 && !ts_node_is_null(right))
                        result = run_node(right, false);
                } else {
                    /* ; or unknown → always run right */
                    if (!ts_node_is_null(right))
                        result = run_node(right, false);
                }
            }
        }
        free(op);
        return result;
    }

    fprintf(stderr, "minibash: node type '%s' not yet implemented\n", type);
    return 0;
}

/* =========================================================================
 * run_program / script reading / main
 * ========================================================================= */

static void run_program(TSNode program)
{
    uint32_t n = ts_node_named_child_count(program);
    for (uint32_t i = 0; i < n; i++)
        run_node(ts_node_named_child(program, i), false);
}

static char *read_script_from_fd(int readfd)
{
    struct stat st;
    if (fstat(readfd, &st) != 0) { utils_error("fstat"); return NULL; }
    char *buf = malloc(st.st_size + 1);
    if (read(readfd, buf, st.st_size) != st.st_size) { utils_error("read"); free(buf); return NULL; }
    buf[st.st_size] = 0;
    return buf;
}

static void execute_script(char *script)
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

int main(int ac, char *av[])
{
    int opt;
    tommy_hashdyn_init(&shell_vars);
    while ((opt = getopt(ac, av, "h")) > 0)
        if (opt == 'h') usage(av[0]);

    parser = ts_parser_new();
    const TSLanguage *bash = tree_sitter_bash();
#define DEFINE_FIELD_ID(name) \
    name##Id = ts_language_field_id_for_name(bash, #name, strlen(#name))
    DEFINE_FIELD_ID(body); DEFINE_FIELD_ID(condition); DEFINE_FIELD_ID(name);
    DEFINE_FIELD_ID(right); DEFINE_FIELD_ID(left); DEFINE_FIELD_ID(operator);
    DEFINE_FIELD_ID(value); DEFINE_FIELD_ID(redirect); DEFINE_FIELD_ID(destination);
    DEFINE_FIELD_ID(variable); DEFINE_FIELD_ID(descriptor);
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
