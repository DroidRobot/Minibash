/*
 * minibash - Phase 2: Variable Expansion + Strings + Variable Assignment
 *
 * Builds on Phase 1.  New in this phase:
 *   - expand_node handles: word, number, raw_string ('...'), string ("..."),
 *     simple_expansion ($VAR, $?, $$), expansion (${VAR}), concatenation,
 *     command_name
 *   - expand_string() for double-quoted strings with embedded expansions
 *   - handle_variable_assignment() for NAME=value
 *   - last_exit_status tracked correctly (128+sig for signals)
 *
 * Passes all Phase 1 tests plus:
 *   015-command-with-quoted-args   (echo "This    is" a "test.")
 *   020-exit-status-var            (echo $?)
 *   022-exit-status-on-crash       (die -segfault; echo $?)
 *   025-sh-pid-var                 (echo $$)
 *   030-variable-env               (echo $LANG / ${LANG})
 *   032-variable                   (NAME=five; echo $NAME)
 *   033-variable-quote             (echo "Hello ${LANG}" vs '${LANG}')
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
 * Job data structures  (unchanged from Phase 1)
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
    job->num_processes_alive = 0;
    job->jid = -1;
    job->pgid = 0;
    job->exit_status = 0;
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
 * SIGCHLD / wait_for_job / handle_child_status  (unchanged from Phase 1)
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
 * NEW IN PHASE 2: String expansion
 *
 * expand_node() is the heart of the shell's "word expansion" logic.
 * Given any tree-sitter node, it returns the runtime string value.
 *
 * Node types handled:
 *   "word"              → raw source text (echo, hello, /bin/ls)
 *   "number"            → raw source text (123)
 *   "raw_string"        → strip surrounding single quotes: 'text' → text
 *   "string"            → double-quoted: expand each child, concat
 *   "simple_expansion"  → $VAR, $?, $$
 *   "expansion"         → ${VAR}
 *   "concatenation"     → join multiple adjacent nodes (e.g., $HOME/.bashrc)
 *   "command_name"      → unwrap the named child
 *
 * expand_string() handles the children of a "string" node.
 * Inside "...", string_content is literal text, while
 * simple_expansion / expansion / command_substitution are expanded.
 * ========================================================================= */

static char *expand_node(TSNode node);

static char *
expand_string(TSNode node)
{
    /* A "string" node's named children are:
     *   string_content  — literal text between quotes
     *   simple_expansion — $VAR inside the string
     *   expansion        — ${VAR} inside the string
     *   command_substitution — $(cmd) inside the string
     * We concatenate all of them in order. */
    char *result = strdup("");
    uint32_t nc = ts_node_named_child_count(node);
    if (nc == 0) return result;

    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_named_child(node, i);
        char *part;
        if (strcmp(ts_node_type(child), "string_content") == 0)
            part = ts_extract_node_text(input, child);
        else
            part = expand_node(child);
        result = utils_string_concat(result, part);
    }
    return result;
}

static char *
expand_node(TSNode node)
{
    if (ts_node_is_null(node))
        return strdup("");

    const char *type = ts_node_type(node);

    /* Plain unquoted word */
    if (strcmp(type, "word") == 0)
        return ts_extract_node_text(input, node);

    /* Numeric literal */
    if (strcmp(type, "number") == 0)
        return ts_extract_node_text(input, node);

    /* Single-quoted string: 'text' → strip the surrounding quotes.
     * Single quotes preserve everything literally — no expansion. */
    if (strcmp(type, "raw_string") == 0)
        return ts_extract_node_text_from_to(input, node, 1, 1);

    /* Double-quoted string: "text $VAR more" → expand children */
    if (strcmp(type, "string") == 0)
        return expand_string(node);

    /* $VAR or $? or $$ */
    if (strcmp(type, "simple_expansion") == 0) {
        uint32_t nc = ts_node_named_child_count(node);
        if (nc == 0) return strdup("");

        TSNode child = ts_node_named_child(node, 0);
        char *result = NULL;

        if (strcmp(ts_node_type(child), "special_variable_name") == 0) {
            char c = ts_extract_single_node_char(input, child);
            if (c == '?') {
                /* $? — exit status of last command */
                asprintf(&result, "%d", last_exit_status);
            } else if (c == '$') {
                /* $$ — shell's own PID */
                asprintf(&result, "%d", (int)getpid());
            } else {
                result = strdup("");
            }
        } else {
            /* $VARNAME — look up in shell_vars, then environment */
            char *varname = ts_extract_node_text(input, child);
            const char *val = hash_get(&shell_vars, varname);
            if (val == NULL) val = getenv(varname);
            result = strdup(val ? val : "");
            free(varname);
        }
        return result;
    }

    /* ${VAR} — braced expansion */
    if (strcmp(type, "expansion") == 0) {
        TSNode varnode = ts_node_child_by_field_id(node, variableId);
        char *varname;
        if (!ts_node_is_null(varnode))
            varname = ts_extract_node_text(input, varnode);
        else
            varname = ts_extract_node_text_from_to(input, node, 2, 1);

        const char *val = hash_get(&shell_vars, varname);
        if (val == NULL) val = getenv(varname);
        char *result = strdup(val ? val : "");
        free(varname);
        return result;
    }

    /* Concatenation: multiple adjacent nodes like $HOME/.bashrc */
    if (strcmp(type, "concatenation") == 0) {
        char *result = strdup("");
        uint32_t nc = ts_node_named_child_count(node);
        for (uint32_t i = 0; i < nc; i++)
            result = utils_string_concat(result, expand_node(ts_node_named_child(node, i)));
        return result;
    }

    /* command_name wraps the actual token */
    if (strcmp(type, "command_name") == 0) {
        uint32_t nc = ts_node_named_child_count(node);
        if (nc > 0) return expand_node(ts_node_named_child(node, 0));
        return ts_extract_node_text(input, node);
    }

    /* Fallback: raw source text */
    return ts_extract_node_text(input, node);
}

/* =========================================================================
 * NEW IN PHASE 2: Variable assignment
 *
 * Handles nodes like:  NAME=value
 * Tree structure:
 *   variable_assignment
 *     name: variable_name   ← "NAME"
 *     value: word/string/...  ← "value" (expanded)
 *
 * Stores the result in shell_vars hash table.
 * ========================================================================= */

static void
handle_variable_assignment(TSNode node)
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
 * build_argv / free_argv  (updated to use expand_node for all arg types)
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
        /* Phase 2: expand_node handles words, strings, variables, etc. */
        argv[argc++] = expand_node(child);
    }

    argv[argc] = NULL;
    return argv;
}

static void
free_argv(char **argv)
{
    if (!argv) return;
    for (int i = 0; argv[i] != NULL; i++) free(argv[i]);
    free(argv);
}

/* =========================================================================
 * Builtins  (unchanged from Phase 1)
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
        if (chdir(dir) != 0) { utils_error("cd: %s: ", dir); last_exit_status = 1; }
        else last_exit_status = 0;
        return true;
    }

    return false;
}

/* =========================================================================
 * run_simple_command  (unchanged from Phase 1)
 * ========================================================================= */

static int
run_simple_command(TSNode node)
{
    char **argv = build_argv(node);
    if (argv[0] == NULL) { free_argv(argv); return 0; }
    if (try_builtin(argv)) { free_argv(argv); return last_exit_status; }

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
        fprintf(stderr, "minibash: spawn failed: %s\n", strerror(rc));
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
 * run_node — dispatcher (Phase 2 additions: variable_assignment)
 * ========================================================================= */

static int
run_node(TSNode node, bool background)
{
    if (ts_node_is_null(node)) return 0;
    const char *type = ts_node_type(node);

    if (strcmp(type, "comment") == 0) return 0;
    if (strcmp(type, "variable_assignment") == 0) {
        handle_variable_assignment(node);
        last_exit_status = 0;
        return 0;
    }
    if (strcmp(type, "command") == 0) return run_simple_command(node);

    fprintf(stderr, "minibash: node type '%s' not yet implemented\n", type);
    return 0;
}

/* =========================================================================
 * run_program / script reading / main  (unchanged from Phase 1)
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
