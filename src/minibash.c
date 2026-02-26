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
#include <stdbool.h>
#include <errno.h>

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
static TSFieldId string_contentId; /* kept for compatibility */
static TSFieldId leftId, operatorId, rightId, descriptorId;

static char *input;         /* to avoid passing the current input around */
static TSParser *parser;    /* a singleton parser instance */
static tommy_hashdyn shell_vars;    /* hash table for shell variables */

static bool shouldexit = false;
static int exit_status = 0;
static int last_exit_status = 0; /* updated after every command */

/* =========================================================================
 * Loop control flow (break / continue)
 * ========================================================================= */

typedef enum {
    EXEC_NORMAL   = 0,
    EXEC_BREAK    = 1,
    EXEC_CONTINUE = 2
} exec_exception_t;

static exec_exception_t exec_exception = EXEC_NORMAL;

/* Forward declarations */
static void handle_child_status(pid_t pid, int status);
static char *read_script_from_fd(int readfd);
static void execute_script(char *script);
static void free_argv(char **argv, int numChild);
static char** build_argv(TSNode child);
static void execute_statement(TSNode child);
static char *expand_value(TSNode node);
static void collect_test_tokens(TSNode node, char **argv, int *argc);

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

/* Possible job status's to use. */
enum job_status {
    FOREGROUND,
    BACKGROUND,
    STOPPED,
    NEEDSTERMINAL,
    TERMINATED_VIA_EXIT,
    TERMINATED_VIA_SIGNAL
};

struct job {
    struct list_elem elem;   /* Link element for jobs list. */
    int     jid;             /* Job id. */
    enum job_status status;  /* Job status. */
    int  num_processes_alive;
    pid_t pid;  /* most-recently-spawned process pid */
    pid_t pgid; /* process group id */
    int exit_status;
};

struct redirect_info {
    char *filename;
    char *redir_text;
    int flags;
    int target_fd;
    bool skip_open;
    bool both_fds;
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
    struct job * job = malloc(sizeof *job);
    job->num_processes_alive = 0;
    job->jid = -1;
    job->pid = 0;
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
    while ((child = waitpid(-1, &status, WUNTRACED|WNOHANG)) > 0) {
        handle_child_status(child, status);
    }
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
    /* Update $? shell variable and last_exit_status global */
    char exit_str[16];
    snprintf(exit_str, sizeof(exit_str), "%d", job->exit_status);
    hash_put(&shell_vars, "?", exit_str);
    last_exit_status = job->exit_status;
}

static struct job*
find_job_by_pid(pid_t pid)
{
    /* Try matching by pgid (works for group leaders) */
    int pgid = getpgid(pid);
    for (int i = 1; i < MAXJOBS; i++) {
        struct job *currJob = get_job_from_jid(i);
        if (currJob != NULL) {
            if (currJob->pgid == pgid) {
                return currJob;
            }
        }
    }
    /* Fallback: match by stored pid (works for last-spawned process) */
    for (int i = 1; i < MAXJOBS; i++) {
        struct job *currJob = get_job_from_jid(i);
        if (currJob != NULL) {
            if (currJob->pid == pid) {
                return currJob;
            }
        }
    }
    return NULL;
}

static void
handle_child_status(pid_t pid, int status)
{
    assert(signal_is_blocked(SIGCHLD));

    struct job *thisJob = find_job_by_pid(pid);
    if (thisJob != NULL) {
        if (WIFEXITED(status)) {
            thisJob->num_processes_alive--;
            thisJob->status = TERMINATED_VIA_EXIT;
            thisJob->exit_status = WEXITSTATUS(status);
        } else if (WIFSIGNALED(status)) {
            thisJob->num_processes_alive--;
            thisJob->status = TERMINATED_VIA_SIGNAL;
            thisJob->exit_status = 128 + WTERMSIG(status);
        } else if (WIFSTOPPED(status)) {
            thisJob->status = STOPPED;
        } else if (WIFCONTINUED(status)) {
            thisJob->status = FOREGROUND;
        }
    }
}

static struct job*
allocate_handler(enum job_status jobStatus)
{
    struct job *thisJob = allocate_job(true);
    thisJob->status = jobStatus;
    thisJob->num_processes_alive = 1;
    return thisJob;
}

/* =========================================================================
 * pipeline_helper - runs a pipeline, optionally with outer redirects
 * ========================================================================= */

static void pipeline_helper(TSNode pipelineNode, char **redirect_filenames,
                            char **redirect_texts, int num_redirects)
{
    int numChild = ts_node_named_child_count(pipelineNode);

    struct job *thisJob = allocate_handler(FOREGROUND);
    thisJob->num_processes_alive = 0;
    thisJob->pgid = 0;

    int stdin_fd = STDIN_FILENO;

    for (int i = 0; i < numChild; i++) {
        TSNode currNode = ts_node_named_child(pipelineNode, i);
        char **argv = build_argv(currNode);
        int pipefds[2];

        if (i != numChild - 1) {
            int r = pipe2(pipefds, O_CLOEXEC);
            if (r == -1) {
                perror("pipe2 failed");
                free_argv(argv, ts_node_named_child_count(currNode));
                return;
            }
        }

        posix_spawn_file_actions_t actions;
        posix_spawn_file_actions_init(&actions);

        if (stdin_fd != STDIN_FILENO) {
            posix_spawn_file_actions_adddup2(&actions, stdin_fd, STDIN_FILENO);
        }

        if (i != numChild - 1) {
            posix_spawn_file_actions_adddup2(&actions, pipefds[1], STDOUT_FILENO);
            /* handle |& (redirect stderr into pipe too) */
            int operatorIndex = 2 * i + 1;
            TSNode op_node = ts_node_child(pipelineNode, operatorIndex);
            if (!ts_node_is_null(op_node)) {
                char *operatorText = ts_extract_node_text(input, op_node);
                if (strcmp(operatorText, "|&") == 0) {
                    posix_spawn_file_actions_adddup2(&actions, pipefds[1], STDERR_FILENO);
                }
                free(operatorText);
            }
        }

        /* track fds we open for redirects */
        int redirfds[16];
        int num_redirfds = 0;

        /* outer redirects (from redirected_statement wrapper) */
        if (redirect_filenames != NULL && redirect_texts != NULL) {
            for (int k = 0; k < num_redirects; k++) {
                bool outputRedir = (strncmp(redirect_texts[k], ">", 1) == 0
                        || strncmp(redirect_texts[k], "&>", 2) == 0);
                bool inputRedir  = (strncmp(redirect_texts[k], "<", 1) == 0);

                if ((outputRedir && i == numChild - 1) || (inputRedir && i == 0)) {
                    if (strncmp(redirect_texts[k], "&>", 2) == 0) {
                        int fd = open(redirect_filenames[k], O_WRONLY | O_CREAT | O_TRUNC, 0644);
                        if (fd >= 0) {
                            posix_spawn_file_actions_adddup2(&actions, fd, STDOUT_FILENO);
                            posix_spawn_file_actions_adddup2(&actions, fd, STDERR_FILENO);
                            redirfds[num_redirfds++] = fd;
                        }
                    } else if (strncmp(redirect_texts[k], ">", 1) == 0) {
                        int fd = open(redirect_filenames[k], O_WRONLY | O_CREAT | O_TRUNC, 0644);
                        if (fd >= 0) {
                            posix_spawn_file_actions_adddup2(&actions, fd, STDOUT_FILENO);
                            redirfds[num_redirfds++] = fd;
                        }
                    } else if (strncmp(redirect_texts[k], "<", 1) == 0) {
                        int fd = open(redirect_filenames[k], O_RDONLY, 0);
                        if (fd >= 0) {
                            posix_spawn_file_actions_adddup2(&actions, fd, STDIN_FILENO);
                            redirfds[num_redirfds++] = fd;
                        }
                    }
                }
            }
        }

        /* per-command redirects inside the pipeline */
        TSNode cmdRedir = ts_node_child_by_field_id(currNode, redirectId);
        if (!ts_node_is_null(cmdRedir)) {
            TSNode cmdDestin   = ts_node_child_by_field_id(cmdRedir, destinationId);
            char *cmdRedirText = ts_extract_node_text(input, cmdRedir);
            char *cmdFilename  = ts_extract_node_text(input, cmdDestin);
            if (strncmp(cmdRedirText, "<", 1) == 0) {
                int fd = open(cmdFilename, O_RDONLY, 0);
                if (fd >= 0) {
                    posix_spawn_file_actions_adddup2(&actions, fd, STDIN_FILENO);
                    redirfds[num_redirfds++] = fd;
                }
            } else if (strncmp(cmdRedirText, ">", 1) == 0) {
                int fd = open(cmdFilename, O_WRONLY | O_CREAT | O_TRUNC, 0644);
                if (fd >= 0) {
                    posix_spawn_file_actions_adddup2(&actions, fd, STDOUT_FILENO);
                    redirfds[num_redirfds++] = fd;
                }
            }
            free(cmdRedirText);
            free(cmdFilename);
        }

        posix_spawnattr_t attrs;
        posix_spawnattr_init(&attrs);

        short flags = POSIX_SPAWN_SETPGROUP;
        posix_spawnattr_setflags(&attrs, flags);
        posix_spawnattr_setpgroup(&attrs, thisJob->pgid);

        int pid;
        int result = posix_spawnp(&pid, argv[0], &actions, &attrs, argv, environ);
        posix_spawn_file_actions_destroy(&actions);
        posix_spawnattr_destroy(&attrs);

        /* close redirect fds after spawn */
        for (int j = 0; j < num_redirfds; j++) {
            close(redirfds[j]);
        }

        if (result == 0) {
            thisJob->num_processes_alive++;
            thisJob->pid = pid;
            if (i == 0) {
                thisJob->pgid = pid;
            }
        } else {
            fprintf(stderr, "posix_spawnp failed in pipeline: %s\n", strerror(result));
        }

        if (stdin_fd != STDIN_FILENO) {
            close(stdin_fd);
        }
        if (i != numChild - 1) {
            close(pipefds[1]);
            stdin_fd = pipefds[0];
        }

        int argc = ts_node_named_child_count(currNode);
        free_argv(argv, argc);
    }

    wait_for_job(thisJob);
    delete_job(thisJob, true);
}

/* =========================================================================
 * strip_quotes_helper - strips surrounding ' or " from a node
 * ========================================================================= */

static void strip_quotes_helper(TSNode arg_node, char **argv, int i)
{
    char *raw = ts_extract_node_text(input, arg_node);
    int len = strlen(raw);
    bool containsDouble = (raw[0] == '"' && raw[len-1] == '"');
    bool containsSingle = (raw[0] == '\'' && raw[len-1] == '\'');
    if (len >= 2 && (containsSingle || containsDouble)) {
        argv[i] = strndup(raw + 1, len - 2);
        free(raw);
    } else {
        argv[i] = raw;
    }
}

/* =========================================================================
 * shell_variable_helper - looks up a variable in shell_vars or environ.
 * Returns a newly allocated string (caller must free).
 * ========================================================================= */

static const char*
shell_variable_helper(char *var_name)
{
    const char *value = hash_get(&shell_vars, var_name);
    if (value == NULL) {
        value = getenv(var_name);
    }
    if (value != NULL) {
        return strdup(value);
    }
    return strdup("");
}

/* =========================================================================
 * expand_value - expand a value node to a newly allocated string.
 * Handles: command_substitution, simple_expansion, expansion, string,
 *          raw_string, concatenation, word, number.
 * ========================================================================= */

static char *
expand_value(TSNode node)
{
    if (ts_node_is_null(node)) return strdup("");
    const char *type = ts_node_type(node);

    /* Command substitution: extract text between $( and ) and run via popen.
     * popen uses /bin/sh -c, which handles pipelines correctly. */
    if (strcmp(type, "command_substitution") == 0) {
        char *cmd_text = ts_extract_node_text_from_to(input, node, 2, 1);
        FILE *fp = popen(cmd_text, "r");
        free(cmd_text);
        char buffer[4096] = {0};
        if (fp != NULL) {
            fread(buffer, 1, sizeof(buffer) - 1, fp);
            int blen = strlen(buffer);
            while (blen > 0 && buffer[blen - 1] == '\n') buffer[--blen] = '\0';
            pclose(fp);
        }
        return strdup(buffer);
    }

    /* Simple variable expansion: $VAR or $? */
    if (strcmp(type, "simple_expansion") == 0) {
        TSNode var_node = ts_node_named_child(node, 0);
        if (ts_node_is_null(var_node)) return strdup("");
        /* Check for special variables */
        if (strcmp(ts_node_type(var_node), "special_variable_name") == 0) {
            char c = ts_extract_single_node_char(input, var_node);
            if (c == '?') {
                char buf[16];
                snprintf(buf, sizeof(buf), "%d", last_exit_status);
                return strdup(buf);
            }
            if (c == '$') {
                char buf[16];
                snprintf(buf, sizeof(buf), "%d", (int)getpid());
                return strdup(buf);
            }
            return strdup("");
        }
        char *varname = ts_extract_node_text(input, var_node);
        char *result  = (char *)shell_variable_helper(varname);
        free(varname);
        return result;
    }

    /* Braced expansion: ${VAR} */
    if (strcmp(type, "expansion") == 0) {
        TSNode var_node = ts_node_named_child(node, 0);
        char *varname = ts_node_is_null(var_node)
                        ? ts_extract_node_text_from_to(input, node, 2, 1)
                        : ts_extract_node_text(input, var_node);
        char *result = (char *)shell_variable_helper(varname);
        free(varname);
        return result;
    }

    /* Double-quoted string: may contain string_content, expansions, cmd subs */
    if (strcmp(type, "string") == 0) {
        char result[4096] = {0};
        int nc = ts_node_child_count(node);
        for (int j = 0; j < nc; j++) {
            TSNode cn = ts_node_child(node, j);
            const char *ct = ts_node_type(cn);
            if (strcmp(ct, "string_content") == 0) {
                char *c = ts_extract_node_text(input, cn);
                strncat(result, c, sizeof(result) - strlen(result) - 1);
                free(c);
            } else if (strcmp(ct, "simple_expansion") == 0 ||
                       strcmp(ct, "expansion") == 0) {
                char *sub = expand_value(cn);
                strncat(result, sub, sizeof(result) - strlen(result) - 1);
                free(sub);
            } else if (strcmp(ct, "command_substitution") == 0) {
                char *sub = expand_value(cn);
                strncat(result, sub, sizeof(result) - strlen(result) - 1);
                free(sub);
            }
        }
        return strdup(result);
    }

    /* Single-quoted string: no expansion, strip the quotes */
    if (strcmp(type, "raw_string") == 0) {
        char *raw = ts_extract_node_text(input, node);
        int len = strlen(raw);
        if (len >= 2 && raw[0] == '\'' && raw[len-1] == '\'') {
            char *r = strndup(raw + 1, len - 2);
            free(raw);
            return r;
        }
        return raw;
    }

    /* Concatenation: expand each part and join */
    if (strcmp(type, "concatenation") == 0) {
        char result[4096] = {0};
        int nc = ts_node_named_child_count(node);
        for (int i = 0; i < nc; i++) {
            char *part = expand_value(ts_node_named_child(node, i));
            strncat(result, part, sizeof(result) - strlen(result) - 1);
            free(part);
        }
        return strdup(result);
    }

    /* word, number, or anything else: extract raw text */
    return ts_extract_node_text(input, node);
}

/* =========================================================================
 * build_argv - build NULL-terminated argv from a command TSNode
 * ========================================================================= */

static char**
build_argv(TSNode child)
{
    int numChild = ts_node_named_child_count(child);
    int arg_index = 0;
    char **argv = malloc(sizeof(char*) * (numChild + 1));

    for (int i = 0; i < numChild; i++) {
        TSNode arg_node = ts_node_named_child(child, i);
        const char *type = ts_node_type(arg_node);

        if (strcmp(type, "file_redirect") == 0) {
            continue;
        }

        if (strcmp(type, "simple_expansion") == 0 || strcmp(type, "expansion") == 0) {
            argv[arg_index++] = expand_value(arg_node);
        } else if (strcmp(type, "string") == 0) {
            /* Double-quoted: expand variables and command substitutions inside */
            char result[4096] = {0};
            bool hasContent = false;
            int stringChildren = ts_node_child_count(arg_node);

            for (int j = 0; j < stringChildren; j++) {
                TSNode child_node = ts_node_child(arg_node, j);
                const char *type_child = ts_node_type(child_node);

                if (strcmp(type_child, "string_content") == 0) {
                    char *content = ts_extract_node_text(input, child_node);
                    strncat(result, content, sizeof(result) - strlen(result) - 1);
                    free(content);
                    hasContent = true;
                } else if (strcmp(type_child, "simple_expansion") == 0 ||
                           strcmp(type_child, "expansion") == 0) {
                    char *expanded = expand_value(child_node);
                    strncat(result, expanded, sizeof(result) - strlen(result) - 1);
                    free(expanded);
                    hasContent = true;
                } else if (strcmp(type_child, "command_substitution") == 0) {
                    char *expanded = expand_value(child_node);
                    strncat(result, expanded, sizeof(result) - strlen(result) - 1);
                    free(expanded);
                    hasContent = true;
                }
            }
            if (!hasContent) {
                strip_quotes_helper(arg_node, argv, arg_index++);
            } else {
                argv[arg_index++] = strdup(result);
            }
        } else if (strcmp(type, "raw_string") == 0) {
            strip_quotes_helper(arg_node, argv, arg_index++);
        } else if (strcmp(type, "command_substitution") == 0) {
            /* Extract text between $( and ) and run via popen.
             * This correctly handles pipelines inside $(...). */
            char *cmd_text = ts_extract_node_text_from_to(input, arg_node, 2, 1);
            FILE *fp = popen(cmd_text, "r");
            free(cmd_text);
            char buffer[4096] = {0};
            if (fp != NULL) {
                fread(buffer, 1, sizeof(buffer) - 1, fp);
                int blen = strlen(buffer);
                while (blen > 0 && buffer[blen - 1] == '\n') buffer[--blen] = '\0';
                pclose(fp);
            }
            argv[arg_index++] = strdup(buffer);
        } else if (strcmp(type, "concatenation") == 0) {
            argv[arg_index++] = expand_value(arg_node);
        } else {
            argv[arg_index++] = ts_extract_node_text(input, arg_node);
        }
    }
    argv[arg_index] = NULL;
    return argv;
}

static void
free_argv(char **argv, int numChild)
{
    (void)numChild;
    for (int i = 0; argv[i] != NULL; i++) {
        free(argv[i]);
    }
    free(argv);
}

/* =========================================================================
 * Control-flow helpers: run_body, execute_condition, run_if/while/for
 * ========================================================================= */

static void
run_body(TSNode body_node)
{
    if (ts_node_is_null(body_node)) return;
    uint32_t nc = ts_node_named_child_count(body_node);
    for (uint32_t i = 0; i < nc; i++) {
        if (exec_exception != EXEC_NORMAL) break;
        execute_statement(ts_node_named_child(body_node, i));
    }
}

static int
execute_condition(TSNode cond_node)
{
    if (ts_node_is_null(cond_node)) return 0;
    execute_statement(cond_node);
    return last_exit_status;
}

static void
run_if_statement(TSNode node)
{
    /* if_statement has field "condition" but NOT "body".
     * Named children: [0]=condition, [1..k]=body stmts, [k+1..]=elif/else clauses
     * elif_clause and else_clause have NO fields at all. */
    TSNode cond = ts_node_child_by_field_id(node, conditionId);
    uint32_t nc = ts_node_named_child_count(node);

    if (execute_condition(cond) == 0) {
        /* Execute body: named children that are not the condition
         * and not elif_clause or else_clause. */
        for (uint32_t i = 0; i < nc; i++) {
            if (exec_exception != EXEC_NORMAL) break;
            TSNode ch = ts_node_named_child(node, i);
            if (ch.id == cond.id) continue;
            const char *ct = ts_node_type(ch);
            if (strcmp(ct, "elif_clause") == 0 || strcmp(ct, "else_clause") == 0) break;
            execute_statement(ch);
        }
        return;
    }

    /* Condition failed — check elif/else */
    for (uint32_t i = 0; i < nc; i++) {
        TSNode ch = ts_node_named_child(node, i);
        const char *ct = ts_node_type(ch);

        if (strcmp(ct, "elif_clause") == 0) {
            /* elif_clause: named child 0 = condition, 1+ = body */
            TSNode ec = ts_node_named_child(ch, 0);
            if (execute_condition(ec) == 0) {
                uint32_t enc = ts_node_named_child_count(ch);
                for (uint32_t j = 1; j < enc; j++) {
                    if (exec_exception != EXEC_NORMAL) break;
                    execute_statement(ts_node_named_child(ch, j));
                }
                return;
            }
        } else if (strcmp(ct, "else_clause") == 0) {
            /* else_clause: all named children are body statements */
            uint32_t enc = ts_node_named_child_count(ch);
            for (uint32_t j = 0; j < enc; j++) {
                if (exec_exception != EXEC_NORMAL) break;
                execute_statement(ts_node_named_child(ch, j));
            }
            return;
        }
    }
}

static void
run_while_statement(TSNode node)
{
    TSNode cond = ts_node_child_by_field_id(node, conditionId);
    TSNode body = ts_node_child_by_field_id(node, bodyId);

    for (;;) {
        if (execute_condition(cond) != 0) break;
        run_body(body);
        if (exec_exception == EXEC_BREAK)    { exec_exception = EXEC_NORMAL; break; }
        if (exec_exception == EXEC_CONTINUE) { exec_exception = EXEC_NORMAL; continue; }
    }
}

static void
run_for_statement(TSNode node)
{
    TSNode var_node = ts_node_child_by_field_id(node, variableId);
    TSNode body     = ts_node_child_by_field_id(node, bodyId);

    if (ts_node_is_null(var_node)) return;
    char *varname = ts_extract_node_text(input, var_node);

    /* Collect the list of values (between "in" and "do") */
    uint32_t nc = ts_node_named_child_count(node);
    char **values = malloc(nc * sizeof(char *));
    int nvalues = 0;

    for (uint32_t i = 0; i < nc; i++) {
        TSNode ch = ts_node_named_child(node, i);
        const char *ct = ts_node_type(ch);
        if (ch.id == var_node.id) continue;
        if (!ts_node_is_null(body) && ch.id == body.id) continue;
        if (strcmp(ct, "do_group") == 0) continue;
        values[nvalues++] = expand_value(ch);
    }

    for (int i = 0; i < nvalues; i++) {
        if (exec_exception != EXEC_NORMAL) break;
        hash_put(&shell_vars, varname, values[i]);
        setenv(varname, values[i], 1);
        run_body(body);
        if (exec_exception == EXEC_BREAK)    { exec_exception = EXEC_NORMAL; break; }
        if (exec_exception == EXEC_CONTINUE) { exec_exception = EXEC_NORMAL; continue; }
    }

    for (int i = 0; i < nvalues; i++) free(values[i]);
    free(values);
    free(varname);
}

/* =========================================================================
 * collect_test_tokens - collect argv tokens from a test_command subtree.
 * Handles both named nodes (expandable/words) and unnamed nodes (operators).
 * ========================================================================= */

static void
collect_test_tokens(TSNode node, char **argv, int *argc)
{
    const char *type = ts_node_type(node);

    /* Expandable nodes - expand variables/cmd substitutions */
    if (strcmp(type, "simple_expansion") == 0 ||
        strcmp(type, "expansion") == 0 ||
        strcmp(type, "string") == 0 ||
        strcmp(type, "raw_string") == 0 ||
        strcmp(type, "command_substitution") == 0 ||
        strcmp(type, "concatenation") == 0) {
        argv[(*argc)++] = expand_value(node);
        return;
    }

    /* Leaf named tokens: word, number, test_operator */
    if (strcmp(type, "word") == 0 ||
        strcmp(type, "number") == 0 ||
        strcmp(type, "test_operator") == 0) {
        argv[(*argc)++] = ts_extract_node_text(input, node);
        return;
    }

    /* Container nodes (binary_expression, unary_expression, etc.):
     * iterate ALL children — named AND unnamed.
     * Unnamed children are operators like =, !=, <, > which must be
     * passed as separate argv tokens to [ ... ]. */
    uint32_t nc = ts_node_child_count(node);
    for (uint32_t i = 0; i < nc; i++) {
        TSNode ch = ts_node_child(node, i);
        if (!ts_node_is_named(ch)) {
            /* Unnamed child: extract text as token, skip [ ] delimiters */
            char *t = ts_extract_node_text(input, ch);
            if (strcmp(t, "[") == 0 || strcmp(t, "]") == 0 ||
                strcmp(t, "[[") == 0 || strcmp(t, "]]") == 0) {
                free(t);
            } else {
                argv[(*argc)++] = t;
            }
        } else {
            collect_test_tokens(ch, argv, argc);
        }
    }
}

/* =========================================================================
 * execute_statement - dispatch a single statement node
 * ========================================================================= */

static void
execute_statement(TSNode child)
{
    const char *type = ts_node_type(child);

    if (strcmp(type, "comment") == 0) {
        return;
    }

    /* ---- simple command ---- */
    else if (strcmp(type, "command") == 0) {
        uint32_t numChild = ts_node_named_child_count(child);
        char **argv = build_argv(child);

        if (argv[0] == NULL) {
            free_argv(argv, numChild);
            return;
        }

        /* Handle builtins */
        if (strcmp(argv[0], "exit") == 0) {
            shouldexit = true;
            exit_status = argv[1] ? atoi(argv[1]) : last_exit_status;
            free_argv(argv, numChild);
            return;
        }
        if (strcmp(argv[0], "break") == 0) {
            exec_exception = EXEC_BREAK;
            last_exit_status = 0;
            free_argv(argv, numChild);
            return;
        }
        if (strcmp(argv[0], "continue") == 0) {
            exec_exception = EXEC_CONTINUE;
            last_exit_status = 0;
            free_argv(argv, numChild);
            return;
        }
        if (strcmp(argv[0], ":") == 0) {
            /* colon builtin: always succeeds */
            last_exit_status = 0;
            free_argv(argv, numChild);
            return;
        }

        struct job *thisJob = allocate_handler(FOREGROUND);
        thisJob->pgid = 0;
        thisJob->num_processes_alive = 0;

        int pid;
        int result = posix_spawnp(&pid, argv[0], NULL, NULL, argv, environ);

        if (result == 0) {
            thisJob->pid  = pid;
            thisJob->pgid = pid;
            thisJob->num_processes_alive = 1;
            wait_for_job(thisJob);
        } else {
            fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(result));
            last_exit_status = 127;
        }

        delete_job(thisJob, true);
        free_argv(argv, numChild);
    }

    /* ---- pipeline ---- */
    else if (strcmp(type, "pipeline") == 0) {
        pipeline_helper(child, NULL, NULL, 0);
    }

    /* ---- redirected_statement: cmd > file, pipeline > file, etc. ---- */
    else if (strcmp(type, "redirected_statement") == 0) {
        TSNode bodyNode = ts_node_child_by_field_id(child, bodyId);
        const char *bodyType = ts_node_type(bodyNode);

        posix_spawn_file_actions_t redirectActions;
        posix_spawn_file_actions_init(&redirectActions);

        int redirects = ts_node_named_child_count(child);
        int fds[16];
        int num_fds_open = 0;
        char *redirect_filenames[16];
        char *redirect_texts[16];
        int num_redirects = 0;

        for (int i = 0; i < redirects; i++) {
            TSNode redirect_child = ts_node_named_child(child, i);
            const char *typeShi = ts_node_type(redirect_child);

            if (strcmp(typeShi, "file_redirect") == 0) {
                TSNode destination  = ts_node_child_by_field_id(redirect_child, destinationId);
                char *filename      = ts_extract_node_text(input, destination);
                char *redir_text    = ts_extract_node_text(input, redirect_child);

                redirect_filenames[num_redirects] = strdup(filename);
                redirect_texts[num_redirects]     = strdup(redir_text);
                num_redirects++;

                TSNode descriptor_node = ts_node_child_by_field_id(redirect_child, descriptorId);
                bool has_descriptor    = !ts_node_is_null(descriptor_node);
                bool both_fds = false;
                bool skip_open = false;
                int flags = 0;
                int target_fd = -1;

                int source_fd = STDOUT_FILENO;
                if (has_descriptor) {
                    char *desc_str = ts_extract_node_text(input, descriptor_node);
                    source_fd = atoi(desc_str);
                    free(desc_str);
                }

                if (strncmp(redir_text, "&>", 2) == 0) {
                    flags     = O_WRONLY | O_CREAT | O_CLOEXEC | O_TRUNC;
                    target_fd = STDOUT_FILENO;
                    both_fds  = true;
                } else if (strncmp(redir_text, ">&", 2) == 0 ||
                           strncmp(redir_text, "2>&", 3) == 0) {
                    bool isfdnumber = true;
                    for (int j = 0; filename[j]; j++) {
                        if (filename[j] < '0' || filename[j] > '9') {
                            isfdnumber = false;
                            break;
                        }
                    }
                    if (isfdnumber) {
                        target_fd = source_fd;
                        skip_open = true;
                    } else {
                        flags     = O_WRONLY | O_CREAT | O_CLOEXEC | O_TRUNC;
                        target_fd = STDOUT_FILENO;
                        both_fds  = true;
                    }
                } else if (strncmp(redir_text, ">>", 2) == 0) {
                    flags     = O_WRONLY | O_CREAT | O_CLOEXEC | O_APPEND;
                    target_fd = source_fd;
                } else if (strncmp(redir_text, ">", 1) == 0) {
                    flags     = O_WRONLY | O_CREAT | O_CLOEXEC | O_TRUNC;
                    target_fd = source_fd;
                } else if (strncmp(redir_text, "<", 1) == 0) {
                    flags     = O_RDONLY | O_CLOEXEC;
                    target_fd = STDIN_FILENO;
                }

                if (skip_open) {
                    int dest_fd = atoi(filename);
                    posix_spawn_file_actions_adddup2(&redirectActions, dest_fd, target_fd);
                } else if (both_fds) {
                    int fd = open(filename, flags, 0666);
                    if (fd != -1) {
                        posix_spawn_file_actions_adddup2(&redirectActions, fd, STDOUT_FILENO);
                        posix_spawn_file_actions_adddup2(&redirectActions, fd, STDERR_FILENO);
                        fds[num_fds_open++] = fd;
                    }
                } else if (target_fd != -1) {
                    int fd = open(filename, flags, 0666);
                    if (fd != -1) {
                        posix_spawn_file_actions_adddup2(&redirectActions, fd, target_fd);
                        fds[num_fds_open++] = fd;
                    }
                }

                free(filename);
                free(redir_text);
            }
        }

        /* Pipeline inside a redirect */
        if (strcmp(bodyType, "pipeline") == 0) {
            pipeline_helper(bodyNode, redirect_filenames, redirect_texts, num_redirects);
            for (int i = 0; i < num_redirects; i++) {
                free(redirect_filenames[i]);
                free(redirect_texts[i]);
            }
        }
        /* Simple command inside a redirect */
        else if (strcmp(bodyType, "command") == 0) {
            char **argv = build_argv(bodyNode);
            int argc    = ts_node_named_child_count(bodyNode);

            if (argv[0] != NULL) {
                if (strcmp(argv[0], ":") == 0) {
                    last_exit_status = 0;
                } else {
                    struct job *thisJob = allocate_handler(FOREGROUND);
                    thisJob->num_processes_alive = 0;
                    thisJob->pgid = 0;

                    int pid;
                    int result = posix_spawnp(&pid, argv[0], &redirectActions,
                                              NULL, argv, environ);

                    if (result == 0) {
                        thisJob->num_processes_alive = 1;
                        thisJob->pid  = pid;
                        thisJob->pgid = pid;
                        wait_for_job(thisJob);
                    } else {
                        fprintf(stderr, "minibash: %s: %s\n", argv[0], strerror(result));
                        last_exit_status = 127;
                    }
                    delete_job(thisJob, true);
                }
            }

            for (int i = 0; i < num_fds_open; i++) close(fds[i]);
            for (int i = 0; i < num_redirects; i++) {
                free(redirect_filenames[i]);
                free(redirect_texts[i]);
            }
            free_argv(argv, argc);
        }
        /* Fallback for other body types */
        else {
            execute_statement(bodyNode);
            for (int i = 0; i < num_fds_open; i++) close(fds[i]);
            for (int i = 0; i < num_redirects; i++) {
                free(redirect_filenames[i]);
                free(redirect_texts[i]);
            }
        }

        posix_spawn_file_actions_destroy(&redirectActions);
    }

    /* ---- variable assignment: VAR=value ---- */
    else if (strcmp(type, "variable_assignment") == 0) {
        TSNode varAssign_name  = ts_node_named_child(child, 0);
        TSNode varAssign_value = ts_node_named_child(child, 1);

        char *var_name  = ts_extract_node_text(input, varAssign_name);
        char *var_value = ts_node_is_null(varAssign_value)
                          ? strdup("")
                          : expand_value(varAssign_value);

        hash_put(&shell_vars, var_name, var_value);
        /* Also export to the real environment so that popen() and
         * posix_spawnp() children can see variables set in this shell. */
        setenv(var_name, var_value, 1);
        free(var_name);
        free(var_value);
        last_exit_status = 0;
    }

    /* ---- list: cmd1 && cmd2  /  cmd1 || cmd2  /  cmd1 ; cmd2 ---- */
    else if (strcmp(type, "list") == 0) {
        /* list has "fields": {} — no field IDs work.
         * Named children: 0=left, 1=right.
         * Operator is an UNNAMED child between them. */
        TSNode left_n  = ts_node_named_child(child, 0);
        TSNode right_n = ts_node_named_child(child, 1);

        /* Find the operator by scanning all (including unnamed) children */
        char *op = NULL;
        uint32_t all_nc = ts_node_child_count(child);
        for (uint32_t i = 0; i < all_nc; i++) {
            TSNode cn = ts_node_child(child, i);
            if (!ts_node_is_named(cn)) {
                char *t = ts_extract_node_text(input, cn);
                if (strcmp(t, "&&") == 0 || strcmp(t, "||") == 0 || strcmp(t, ";") == 0) {
                    op = t;
                    break;
                }
                free(t);
            }
        }

        if (!ts_node_is_null(left_n)) execute_statement(left_n);

        if (op != NULL) {
            if (strcmp(op, "&&") == 0) {
                if (last_exit_status == 0 && !ts_node_is_null(right_n))
                    execute_statement(right_n);
            } else if (strcmp(op, "||") == 0) {
                if (last_exit_status != 0 && !ts_node_is_null(right_n))
                    execute_statement(right_n);
            } else {
                if (!ts_node_is_null(right_n)) execute_statement(right_n);
            }
            free(op);
        } else if (!ts_node_is_null(right_n)) {
            execute_statement(right_n);
        }
    }

    /* ---- if / elif / else ---- */
    else if (strcmp(type, "if_statement") == 0) {
        run_if_statement(child);
    }

    /* ---- while loop ---- */
    else if (strcmp(type, "while_statement") == 0) {
        run_while_statement(child);
    }

    /* ---- for loop ---- */
    else if (strcmp(type, "for_statement") == 0) {
        run_for_statement(child);
    }

    /* ---- compound_statement or do_group: just run the body ---- */
    else if (strcmp(type, "do_group") == 0 ||
             strcmp(type, "compound_statement") == 0) {
        run_body(child);
    }

    /* ---- negated command: ! cmd ---- */
    else if (strcmp(type, "negated_command") == 0) {
        uint32_t nc = ts_node_named_child_count(child);
        for (uint32_t i = 0; i < nc; i++)
            execute_statement(ts_node_named_child(child, i));
        last_exit_status = (last_exit_status == 0) ? 1 : 0;
    }

    /* ---- test_command: [ ... ] ---- */
    else if (strcmp(type, "test_command") == 0) {
        /* Build argv: "[", expanded args..., "]"
         * Iterate only named children of test_command (the [ ] are unnamed).
         * For each named child, collect_test_tokens recursively expands
         * variables/cmd-subs and collects operator tokens. */
        char *argv[128];
        int argc = 0;
        argv[argc++] = strdup("[");

        uint32_t nc = ts_node_named_child_count(child);
        for (uint32_t i = 0; i < nc; i++) {
            collect_test_tokens(ts_node_named_child(child, i), argv, &argc);
        }
        argv[argc++] = strdup("]");
        argv[argc] = NULL;

        struct job *thisJob = allocate_handler(FOREGROUND);
        thisJob->pgid = 0;
        thisJob->num_processes_alive = 0;

        int pid;
        int result = posix_spawnp(&pid, argv[0], NULL, NULL, argv, environ);
        if (result == 0) {
            thisJob->pid  = pid;
            thisJob->pgid = pid;
            thisJob->num_processes_alive = 1;
            wait_for_job(thisJob);
        } else {
            fprintf(stderr, "minibash: [: %s\n", strerror(result));
            last_exit_status = 1;
        }
        delete_job(thisJob, true);
        for (int i = 0; i < argc; i++) free(argv[i]);
    }

    else {
        fprintf(stderr, "node type `%s` not implemented\n", ts_node_type(child));
    }
}

/* =========================================================================
 * run_program - execute all top-level statements
 * ========================================================================= */

static void
run_program(TSNode program)
{
    uint32_t count = ts_node_named_child_count(program);
    for (uint32_t i = 0; i < count; i++) {
        if (shouldexit || exec_exception != EXEC_NORMAL) break;
        execute_statement(ts_node_named_child(program, i));
    }
}

/* =========================================================================
 * read_script_from_fd, execute_script, main
 * ========================================================================= */

static char *
read_script_from_fd(int readfd)
{
    struct stat st;
    if (fstat(readfd, &st) != 0) {
        utils_error("Could not fstat input");
        return NULL;
    }

    char *userinput = malloc(st.st_size + 1);
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

    /* Store shell PID as $$ */
    char shellPID[16];
    snprintf(shellPID, sizeof(shellPID), "%d", getpid());
    hash_put(&shell_vars, "$", shellPID);

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
    DEFINE_FIELD_ID(descriptor);
    DEFINE_FIELD_ID(string_content);

    ts_parser_set_language(parser, bash);

    list_init(&job_list);
    signal_set_handler(SIGCHLD, sigchld_handler);

    /* Read/eval loop */
    for (;;) {
        if (shouldexit)
            break;

        /* If you fail this assertion, you were about to enter readline()
         * while SIGCHLD is blocked. */
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
            if (av[optind] != NULL)
                close(readfd);
            if (userinput == NULL)
                utils_fatal_error("Could not read input");
        }
        execute_script(userinput);
        free(userinput);
        if (av[optind] != NULL)
            shouldexit = true;
    }

    ts_parser_delete(parser);
    tommy_hashdyn_foreach(&shell_vars, hash_free);
    tommy_hashdyn_done(&shell_vars);
    return exit_status;
}
