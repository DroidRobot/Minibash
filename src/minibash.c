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
static TSFieldId string_contentId;//need this for quotes
static TSFieldId leftId, operatorId, rightId, descriptorId;

static char *input;         // to avoid passing the current input around
static TSParser *parser;    // a singleton parser instance 
static tommy_hashdyn shell_vars;        // a hash table containing the internal shell variables
                                        
static bool shouldexit = false;
static int exit_status = 0;

typedef enum {
    EXEC_NORMAL   = 0,
    EXEC_BREAK    = 1,
    EXEC_CONTINUE = 2
} exec_exception_t;

static exec_exception_t exec_exception = EXEC_NORMAL;

static void handle_child_status(pid_t pid, int status);
static char *read_script_from_fd(int readfd);
static void execute_script(char *script);
static void free_argv(char **argv, int numChild);
static char** build_argv(TSNode child);
static void run_single_node(TSNode node);
static void if_statement_handler(TSNode ifNode);


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
    pid_t pid; /* need to map job to its child process*/
    pid_t pgid; /* need to map job to its child process*/
    int exit_status;//store exit code


    /* Add additional fields here as needed. */
};

//this is necessary for having the helper methods
//there has to eb a way to tell the difference
//between fd to file and fd to fd
struct redirect_info{
    char *filename;//destionation string
    char *redir_text;// full redirect text
    int flags;//open() flags
    int target_fd;//fd that is being redirected
    bool skip_open;//true for fd to fd
    bool both_fds;//true for redirects that target both stdout and stderr
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
    job->pid = -1;
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

        if (child != -1)
            handle_child_status(child, status);
        else
            utils_fatal_error("waitpid failed, see code for explanation");
    }
    exit_status = job->exit_status;  // sync global
    char exit_str[16];
    snprintf(exit_str, sizeof(exit_str), "%d", job->exit_status);
    hash_put(&shell_vars, "?", exit_str);
}

/*
 * Iterate through all possible jobs and check if a job has a PID that matches
 */
static struct job*
find_job_by_pid(pid_t pid)
{
    //TODO: is iterating through all MAXJOBS the right approach?
    //can we keep track of how many jobs there are from the list?
    //check pgid first
    int pgid = getpgid(pid);
    for(int i = 1;i<MAXJOBS;i++){
        struct job *currJob = get_job_from_jid(i);
        if(currJob != NULL){//dont dereference null pointer
            if(currJob->pgid == pgid){
                return currJob;
            }
        }
    }
    //lookup by normal pid
    for(int i = 1;i<MAXJOBS;i++){
        struct job *currJob = get_job_from_jid(i);
        if(currJob != NULL){//dont dereference null pointer
            if(currJob->pid == pid){
                return currJob;
            }
        }
    }

    return NULL;//if not found return null
}



/*
 * When a child changes state waitpid captures 
 * that state as int status. 
 * handle_child_status needs to use that int and 
 * translate it to WIF* Macro
 */
static void
handle_child_status(pid_t pid, int status)
{
    assert(signal_is_blocked(SIGCHLD));

    struct job *thisJob = find_job_by_pid(pid);
    if(thisJob != NULL){
        //process exited normally and is dead 
        //set job status TERMINATED_VIA_EXIT
        if(WIFEXITED(status)){
            thisJob->num_processes_alive--;
            thisJob->status = TERMINATED_VIA_EXIT;
            //this is what captures the exit coe
            thisJob->exit_status = WEXITSTATUS(status);
        }

        //process exited by a signal and is dead
        //set job status TERMINATED_VIA_SIGNAL
        else if(WIFSIGNALED(status)){
            thisJob->num_processes_alive--;
            thisJob->status = TERMINATED_VIA_SIGNAL;
            //this is from from the handout directly
            //handles the SIGNAL sent and adds 128 for some reaosn
            //segfault: SIGSEGV: 11 + 128 = 139 , etc
            thisJob->exit_status = 128 + WTERMSIG(status);
        }

        //process is paused but still alive
        else if(WIFSTOPPED(status)){
            thisJob->status = STOPPED;
        }

        //"resume" stopped process
        else if(WIFCONTINUED(status)){
            thisJob->status = FOREGROUND;
            //TODO: this might have to be BACKGROUND as well^^^
        }


    }

}

static struct job* 
allocate_handler(enum job_status jobStatus){
    //allocate_job
    struct job *thisJob = allocate_job(true);
    thisJob->status = jobStatus;
    thisJob->num_processes_alive = 1;//this might be 0?
    return thisJob;
}


static int
execute_condition(TSNode cond_node)
{
    if (ts_node_is_null(cond_node)) return 0;
    run_single_node(cond_node);
    return exit_status;
}


static void
run_body(TSNode body_node)
{
    if (ts_node_is_null(body_node)) return;
    uint32_t nc = ts_node_named_child_count(body_node);
    for (uint32_t i = 0; i < nc; i++) {
        if (exec_exception != EXEC_NORMAL) break;
        run_single_node(ts_node_named_child(body_node, i));
    }
}

static void if_statement_handler(TSNode ifNode)
{
    /*
     * AST of an if else
     * if true; then 
     *      echo true is true
     * fi
     *
     * if_statement
     *      condition: command "true" <-- new condition field
     *      command "echo true is true"
     *
     *
     */
    //run the if statement
    TSNode condition = ts_node_child_by_field_id(ifNode, conditionId);
    run_single_node(condition);

    const char *exitVal = hash_get(&shell_vars, "?");
    //did we take the branch?
    bool tookBranch = false;
    if(exitVal != NULL 
            && strcmp(exitVal, "0") == 0){
        tookBranch = true;
    }

    //IF
    //if the condition was true run the "then" body
    if(tookBranch){
        int num = ts_node_named_child_count(ifNode);
        for(int i = 0;i<num;i++){
            TSNode statement = ts_node_named_child(ifNode, i);
            const char *statementType = ts_node_type(statement);
            if(ts_node_eq(statement, condition)){
                continue;
            }
            if(strcmp(statementType, "elif_clause") == 0){
                continue;
            }
            if(strcmp(statementType, "else_clause") == 0){
                continue;
            }
            run_single_node(statement);
        }
    }

    //ELIF
    if(!tookBranch){
        int num = ts_node_named_child_count(ifNode);
        for(int i = 0;i<num && !tookBranch;i++){
            TSNode statement = ts_node_named_child(ifNode, i);
            const char *statementType = ts_node_type(statement);

            if(strcmp(statementType, "elif_clause") != 0){
                continue;
            }
            else{
                TSNode elifClause = ts_node_named_child(statement,0);
                run_single_node(elifClause);
            }

            const char *elifExit = hash_get(&shell_vars, "?");
            if(elifExit != NULL && strcmp(elifExit, "0") == 0){
                tookBranch = true;
                int numElif = ts_node_named_child_count(statement);
                for(int j = 0;j<numElif;j++){
                    TSNode elifStatement = ts_node_named_child(statement,j);
                    run_single_node(elifStatement);
                }
            }
        }

    }
    //ELSE
    //if nothing matches 
    //meaning did not take the if or elif
    //run the else
    if(!tookBranch){
        int num = ts_node_named_child_count(ifNode);
        for(int i = 0;i<num;i++){
            TSNode clause = ts_node_named_child(ifNode, i);
            const char *clauseType = ts_node_type(clause);
            if(strcmp(clauseType, "else_clause") != 0){
                continue;
            }
            else{
                int numElse = ts_node_named_child_count(clause);
                for(int j = 0;j<numElse;j++){
                    run_single_node(ts_node_named_child(clause,j));
                }
            }
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
                snprintf(buf, sizeof(buf), "%d", exit_status);
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

static void pipeline_helper(TSNode pipelineNode, char **redirect_filenames, char ** redirect_texts,int num_redirects)
{
    int numChild = ts_node_named_child_count(pipelineNode);

    struct job *thisJob = allocate_handler(FOREGROUND);
    thisJob->num_processes_alive = 0;
    thisJob->pgid = 0;

    int stdin_fd = STDIN_FILENO;
    //ls | cat 
    //stdout of ls goes into stdin vim 
    for(int i = 0;i<numChild;i++){
        TSNode currNode = ts_node_named_child(pipelineNode,i);

        //build argv for each command between | pipes
        char **argv = build_argv(currNode);
        int pipe[2];
        //you must check if the last child is a pipe
        //ls | cat |
        if(i != numChild - 1){
            int lastPipe = pipe2(pipe, O_CLOEXEC);
            if(lastPipe == -1){
                perror("pipe2 failed");
                return;
            }
        }

        //file actions for handling pipes stdin and stdout
        posix_spawn_file_actions_t actions;
        posix_spawn_file_actions_init(&actions) ;

        if(stdin_fd != STDIN_FILENO){
            posix_spawn_file_actions_adddup2(&actions, stdin_fd, STDIN_FILENO);
        }
        //gotta check for |& specifically so that stderr fd can be created
        if (i != numChild-1){
            posix_spawn_file_actions_adddup2(&actions, pipe[1], STDOUT_FILENO);
            //must now handle |&
            int operatorIndex = 2*i +1;//get the index of the operator 
                                       //assumes i is at a command
            TSNode op_node = ts_node_child(pipelineNode, operatorIndex);
            if(!ts_node_is_null(op_node)){
                char *operatorText = ts_extract_node_text(input, op_node);
                if(strcmp(operatorText, "|&") == 0){
                    posix_spawn_file_actions_adddup2(&actions, pipe[1], STDERR_FILENO);
                }
                free(operatorText);
            }

        }

        //we have to track the fds to close after they spawn
        int redirfds[16];
        int num_redirfds = 0;

        //what about redirects in pipes???? handled here.
        if(redirect_filenames != NULL && redirect_texts != NULL){
            for(int k = 0;k<num_redirects;k++){
                //just to make it simple to read
                bool outputRedir = (strncmp(redirect_texts[k], ">", 1) == 0 
                        ||strncmp(redirect_texts[k], "&>", 2) == 0);
                bool inputRedir = (strncmp(redirect_texts[k], "<", 1) == 0);

                if((outputRedir && i == numChild-1) || (inputRedir && i == 0)){
                    //Case for both stdout and stderr in a pipe
                    if(strncmp(redirect_texts[k], "&>", 2) == 0){
                        int fd = open(redirect_filenames[k], O_WRONLY | O_CREAT | O_TRUNC, 0644);
                        if(fd >= 0){
                            posix_spawn_file_actions_adddup2(&actions, fd, STDOUT_FILENO);
                            posix_spawn_file_actions_adddup2(&actions, fd, STDERR_FILENO);
                            redirfds[num_redirfds] = fd; 
                            num_redirfds++;
                        }
                    }
                    //Case for both stdout  in a pipe
                    else if(strncmp(redirect_texts[k], ">", 1) == 0){
                        int fd = open(redirect_filenames[k], O_WRONLY | O_CREAT | O_TRUNC, 0644);
                        if(fd >= 0){
                            posix_spawn_file_actions_adddup2(&actions, fd, STDOUT_FILENO);
                            redirfds[num_redirfds] = fd; 
                            num_redirfds++;
                        }
                    }
                    //Case for both stdin  in a pipe
                    else if(strncmp(redirect_texts[k], "<", 1) == 0){
                        int fd = open(redirect_filenames[k], O_RDONLY, 0);
                        if(fd >= 0){
                            posix_spawn_file_actions_adddup2(&actions, fd, STDIN_FILENO);
                            redirfds[num_redirfds] = fd; 
                            num_redirfds++;
                        }
                    }
                }
            }
        }


        posix_spawnattr_t attrs;
        //redirects can also be inside the command node
        TSNode cmdRedir = ts_node_child_by_field_id(currNode, redirectId);
        if(!ts_node_is_null(cmdRedir)){
            TSNode cmdDestin = ts_node_child_by_field_id(cmdRedir, destinationId);
            char *cmdRedirText = ts_extract_node_text(input, cmdRedir);
            char *cmdFilename = expand_value(cmdDestin);
            if(strncmp(cmdRedirText, "<", 1) == 0){
                int fd = open(cmdFilename, O_RDONLY, 0);
                if(fd >= 0){
                    posix_spawn_file_actions_adddup2(&actions, fd, STDIN_FILENO);
                    redirfds[num_redirfds++] = fd;
                }
            }
            else if(strncmp(cmdRedirText, ">", 1) == 0){
                int fd = open(cmdFilename, O_WRONLY | O_CREAT | O_TRUNC, 0644);
                if(fd >=0){
                    posix_spawn_file_actions_adddup2(&actions, fd, STDOUT_FILENO);
                    redirfds[num_redirfds++] = fd;
                }
            }
            free(cmdRedirText);
            free(cmdFilename);
        }

        posix_spawnattr_init(&attrs);

        short flags = POSIX_SPAWN_SETPGROUP;
        posix_spawnattr_setflags(&attrs, flags);

        //first process should set the process group id to its own pid
        posix_spawnattr_setpgroup(&attrs, thisJob->pgid);

        //creat children
        int pid;
        // printf("command after pipe: %s\n", argv[0]);

        int result = posix_spawnp(&pid, argv[0], &actions,&attrs,argv,environ);
        //cleanup fds
        posix_spawn_file_actions_destroy(&actions);
        posix_spawnattr_destroy(&attrs);

        //now, close all the redirect fds after posix_spawnp call
        for(int j = 0;j<num_redirfds;j++){
            close(redirfds[j]);
        }
        

        if(result == 0){//command after the pipe was successful
            thisJob->num_processes_alive++;
            thisJob->pid = pid;//needed?
                               //first process should set the process group id to its own pid
            if(i==0){
                thisJob->pgid = pid;
            }
        }
        else{
            printf("posix didnt work in pipe");
        }

        // printf("i: %d\n", i);
        // printf("numchild: %d\n",numChild);
        if(stdin_fd != STDIN_FILENO){
            close(stdin_fd);
        }
        if (i != numChild -1){
            close(pipe[1]);//close stdout of current pipe
            stdin_fd = pipe[0];
        }

        //free args
        int argc = ts_node_named_child_count(currNode);
        free_argv(argv, argc);

    }
    wait_for_job(thisJob);
    delete_job(thisJob, true);

}
static char** build_argv(TSNode child)
{
    int numChild = ts_node_named_child_count(child);
    int arg_index = 0;
    char **argv = malloc(sizeof(char*) * (numChild+1));

    for(int i = 0; i < numChild; i++){
        TSNode arg_node = ts_node_named_child(child, i);
        if(strcmp(ts_node_type(arg_node), "file_redirect") == 0){
            continue;
        }
        argv[arg_index++] = expand_value(arg_node);
    }
    argv[arg_index] = NULL;
    return argv;
}


//handles freeing argv
static void free_argv(char **argv, int numChild)
{
    for(int i = 0;argv[i] != NULL;i++){
        free(argv[i]);//free text returned by ts_extract_node_text
    }
    free(argv);//free 
}
//gets the exit status of a popen
static int run_popen_helper(const char *cmd){
    FILE *fp = popen(cmd, "r");
    if(fp == NULL){
        return 1;
    }
    int status = pclose(fp);
    return WEXITSTATUS(status);
}
//this has to do essentially what run_program does without the forloop
//but for a single TSNode
//why?? because of if statements
static void run_single_node(TSNode node)
{
    const char *type = ts_node_type(node);

    if (strcmp(type, "comment") == 0) {
        return;
    }
    else if (strcmp(type, "command") == 0) {
        int numChild = ts_node_named_child_count(node);
        char **argv = build_argv(node);
        if (strcmp(argv[0], "exit") == 0) {
            shouldexit = true;
            exit_status = 0;
            free_argv(argv, numChild);
            return;
        }
        if (strcmp(argv[0], ":") == 0) {
            hash_put(&shell_vars, "?", "0");
            exit_status = 0;
            free_argv(argv, numChild);
            return;
        }
        if (strcmp(argv[0], "break") == 0) { 
            exec_exception = EXEC_BREAK; 
            free_argv(argv, numChild); 
            return; 
        }
        if (strcmp(argv[0], "continue") == 0) { 
            exec_exception = EXEC_CONTINUE; 
            free_argv(argv, numChild); 
            return; 
        }


        struct job *thisJob = allocate_handler(FOREGROUND);

        int pid;
        int result = posix_spawnp(&pid, argv[0], NULL, NULL, argv, environ);

        if (result == 0) {
            thisJob->pid = pid;
            wait_for_job(thisJob);  // syncs exit_status via fix 1
        } else {
            perror("posix_spawnp didnt work");
            thisJob->num_processes_alive--;
        }

        delete_job(thisJob, true);
        free_argv(argv, numChild);
    }
    else if (strcmp(type, "pipeline") == 0) {
        pipeline_helper(node, NULL, NULL, 0);
    }
    else if (strcmp(type, "test_command") == 0) {
        char *raw = ts_extract_node_text(input, node);
        int exitCode = run_popen_helper(raw);
        free(raw);
        exit_status = exitCode;  // sync global
        char exitStr[16];
        snprintf(exitStr, sizeof(exitStr), "%d", exitCode);
        hash_put(&shell_vars, "?", exitStr);
    }
    else if (strcmp(type, "variable_assignment") == 0) {
        TSNode varAssign_name  = ts_node_named_child(node, 0);
        TSNode varAssign_value = ts_node_named_child(node, 1);

        char *var_name  = ts_extract_node_text(input, varAssign_name);
        char *var_value = expand_value(varAssign_value);  // expand, not raw text

        hash_put(&shell_vars, var_name, var_value);
        setenv(var_name, var_value, 1);

        free(var_name);
        free(var_value);
    }
    else if (strcmp(type, "list") == 0) {
        TSNode left_n  = ts_node_named_child(node, 0);
        TSNode right_n = ts_node_named_child(node, 1);

        char *op = NULL;
        uint32_t all_nc = ts_node_child_count(node);
        for (uint32_t i = 0; i < all_nc; i++) {
            TSNode cn = ts_node_child(node, i);
            if (!ts_node_is_named(cn)) {
                char *t = ts_extract_node_text(input, cn);
                if (strcmp(t, "&&") == 0 || strcmp(t, "||") == 0 || strcmp(t, ";") == 0) {
                    op = t;
                    break;
                }
                free(t);
            }
        }

        if (!ts_node_is_null(left_n)) run_single_node(left_n);

        if (op != NULL) {
            if (strcmp(op, "&&") == 0) {
                if (exit_status == 0 && !ts_node_is_null(right_n))
                    run_single_node(right_n);
            } else if (strcmp(op, "||") == 0) {
                if (exit_status != 0 && !ts_node_is_null(right_n))
                    run_single_node(right_n);
            } else {
                if (!ts_node_is_null(right_n)) run_single_node(right_n);
            }
            free(op);
        } else if (!ts_node_is_null(right_n)) {
            run_single_node(right_n);
        }
    }
    else if (strcmp(type, "if_statement") == 0) {
        if_statement_handler(node);
    }
    else if (strcmp(type, "while_statement") == 0) {
        run_while_statement(node);
    }
    else if (strcmp(type, "for_statement") == 0) {
        run_for_statement(node);
    }
    else if (strcmp(type, "break_statement") == 0) {
        exec_exception = EXEC_BREAK;
    }
    else if (strcmp(type, "continue_statement") == 0) {
        exec_exception = EXEC_CONTINUE;
    }
    else if (strcmp(type, "do_group") == 0 ||
             strcmp(type, "compound_statement") == 0) {
        run_body(node);
    }
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

        if(strcmp(type, "comment") == 0){
            continue;
        }
        //simple command
        else if(strcmp(type, "command") == 0){
            //extract the arguments

            // char *cmd_name = ts_extract_node_text(input, child);
            // check if its exit
            uint32_t numChild = ts_node_named_child_count(child);
            char **argv = build_argv(child);
            if(strcmp(argv[0], "exit") == 0){
                shouldexit = true;
                exit_status = 0;
                free_argv(argv,numChild);
                return;
            }
            if(strcmp(argv[0], ":") == 0){
                hash_put(&shell_vars, "?", "0");
                free_argv(argv, numChild);
                continue;//do not return here! we may not be at the end fo the for loop
            }
            if (strcmp(argv[0], "break") == 0) { 
                exec_exception = EXEC_BREAK; 
                free_argv(argv, numChild); 
                return; 
            }
            if (strcmp(argv[0], "continue") == 0) { 
                exec_exception = EXEC_CONTINUE; 
                free_argv(argv, numChild); 
                return; 
            }

            struct job *thisJob = allocate_handler(FOREGROUND); 

            int pid;
            int result = posix_spawnp(&pid, argv[0], NULL, NULL, argv, environ);

            //wait for thisJob to be done call wait_for_thisJob()
            if(result == 0){
                thisJob->pid = pid;
                wait_for_job(thisJob);
            }else{
                perror("posix_spawnp didnt work");
                thisJob->num_processes_alive--;
            }

            //cleanup memory
            delete_job(thisJob, true);
            free_argv(argv, numChild);

        } 
        else if(strcmp(type, "pipeline") == 0){
            pipeline_helper(child, NULL, NULL, 0);
        }
        else if(strcmp(type, "redirected_statement") == 0){
            //get the body of the node
            TSNode bodyNode = ts_node_child_by_field_id(child, bodyId);
            // char **argv = build_argv(bodyNode);
            // int argc = ts_node_named_child_count(bodyNode);
            const char *bodyType = ts_node_type(bodyNode);


            //start actions like from piping
            posix_spawn_file_actions_t redirectActions;
            posix_spawn_file_actions_init(&redirectActions);


            //count how many redirects
            int redirects = ts_node_named_child_count(child);
            int fds[16];
            int num_fds_open = 0;
            char *redirect_filenames[16];
            char *redirect_texts[16];
            int num_redirects = 0;
            for(int i = 0;i<redirects;i++){
                //child in "ls > out.txt" is: "> out.txt"
                TSNode redirect_child = ts_node_named_child(child, i);
                const char *typeShi = ts_node_type(redirect_child);//why typeShi? bc type was taken

                bool both_fds = false;
                //need this loop for multiple file redirects in a single command: ls > yo.txt > wc
                if(strcmp(typeShi, "file_redirect") == 0){
                    TSNode destination = ts_node_child_by_field_id(redirect_child, destinationId);
                    char *filename = expand_value(destination);
                    char *redir_text = ts_extract_node_text(input, redirect_child);

                    //store first redirect info for pipeline case
                    redirect_filenames[num_redirects] = strdup(filename);
                    redirect_texts[num_redirects] = strdup(redir_text);
                    num_redirects++;
                    //why strdup? bc they get free later

                    TSNode descriptor_node = ts_node_child_by_field_id(redirect_child,descriptorId);
                    bool has_descriptor = !ts_node_is_null(descriptor_node);

                    //hold the flags in a variable and then just go through
                    //the bottom if else block to fill it in based on
                    //why? bc it would look unreadable if u didnt 
                    // int fd;
                    int flags = 0;
                    int target_fd;
                    bool skip_open = false; //MUST have this for the fd to fd redirects >&N

                    //check if there is a file descriptor
                    int source_fd = STDOUT_FILENO;
                    if(has_descriptor){
                        char *desc_str = ts_extract_node_text(input, descriptor_node);
                        source_fd = atoi(desc_str);//convert int to string
                        free(desc_str);
                    }

                    //check the flags and set the target_fd
                    if(strncmp(redir_text,"&>",2) == 0){
                        //THIS REDIRECTS BOTH STDOUT AND STDERR
                        flags = O_WRONLY | O_CREAT | O_CLOEXEC | O_TRUNC;
                        target_fd = STDOUT_FILENO;
                        both_fds = true;
                    }
                    else if(strncmp(redir_text,">&",2) == 0  || strncmp(redir_text,"2>&",3) == 0){
                        // >&N or 2>&N means fd to fd
                        //this body basically asks is it a number or &?
                        bool isfdnumber = true;
                        for(int j = 0;filename[j];j++){
                            if(filename[j] < '0' || filename[j] > '9'){
                                isfdnumber = false;
                                break;
                            }
                        }
                        if(isfdnumber){
                            target_fd = source_fd;
                            skip_open = true;
                        }
                        else{
                            //for >& or &>, redirecting stdout and stderr
                            flags = O_WRONLY | O_CREAT | O_CLOEXEC | O_TRUNC;
                            target_fd = STDOUT_FILENO;
                            both_fds = true;
                        }
                    }
                    //normal cases
                    else if(strncmp(redir_text, ">", 1) == 0){
                        flags = O_WRONLY | O_CREAT | O_CLOEXEC | O_TRUNC;
                        target_fd = STDOUT_FILENO;
                    }
                    else if(strncmp(redir_text, "<", 1) == 0){
                        flags = O_RDONLY | O_CLOEXEC;
                        target_fd = STDIN_FILENO;
                    }



                    //do we have to open files?not if its fd to fd (>& or 2>&)
                    if(skip_open){
                        int dest_fd = atoi(filename);
                        posix_spawn_file_actions_adddup2(&redirectActions,dest_fd,target_fd);
                    }
                    else if(both_fds){
                        //this is the case for &>, open file and then must dup2 
                        //TWICE for both STDOUT AND STDERR!!!
                        int fd = open(filename, flags, 0666);
                        if (fd == -1){
                            printf("open failed");
                        }
                        else{
                            posix_spawn_file_actions_adddup2(&redirectActions, fd, STDOUT_FILENO);
                            posix_spawn_file_actions_adddup2(&redirectActions, fd, STDERR_FILENO);
                            fds[num_fds_open++] = fd;
                        }
                    }
                    else if( target_fd != -1){
                        int fd = open(filename, flags, 0666);
                        if (fd == -1){
                            printf("open failed");
                        }
                        else{
                            posix_spawn_file_actions_adddup2(&redirectActions, fd, target_fd);
                            fds[num_fds_open] = fd;
                            num_fds_open++;
                        }
                    }

                    //cleanup
                    free(filename);
                    free(redir_text);
                }
            }

            //PIPELINES INSIDE REDIRECTS
            if(strcmp(bodyType, "pipeline") == 0){
                pipeline_helper(bodyNode, redirect_filenames, redirect_texts, num_redirects);

                for(int i = 0;i< num_redirects;i++){
                    free(redirect_filenames[i]);
                    free(redirect_texts[i]);
                }
            }
            //COMMANDS INSIDE REDIRECT
            else if(strcmp(bodyType, "command") == 0){
                //create the job
                char **argv = build_argv(bodyNode);
                int argc = ts_node_named_child_count(bodyNode);

                struct job *thisJob = allocate_handler(FOREGROUND);
                thisJob->num_processes_alive = 0;

                int pid;
                int result = posix_spawnp(&pid, argv[0], &redirectActions, NULL, argv, environ);

                if(result == 0){
                    thisJob->num_processes_alive++;
                    thisJob->pid = pid;
                    wait_for_job(thisJob);
                }
                else{
                    printf("somethin failed");
                }
                for(int i = 0;i<num_fds_open;i++){
                    close(fds[i]);
                }

                delete_job(thisJob,true);
                free_argv(argv,argc);
                for(int i = 0;i<num_redirects;i++){
                    free(redirect_filenames[i]);
                    free(redirect_texts[i]);
                }
            }
            posix_spawn_file_actions_destroy(&redirectActions);
        }
        
        else if (strcmp(type, "variable_assignment") == 0) {
            TSNode varAssign_name  = ts_node_named_child(child, 0);
            TSNode varAssign_value = ts_node_named_child(child, 1);

            char *var_name  = ts_extract_node_text(input, varAssign_name);
            char *var_value = expand_value(varAssign_value);  // expand, not raw text

            hash_put(&shell_vars, var_name, var_value);
            setenv(var_name, var_value, 1);

            free(var_name);
            free(var_value);
        }
        else if(strcmp(type, "if_statement") == 0){
            if_statement_handler(child);
        }
   
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

            if (!ts_node_is_null(left_n)) run_single_node(left_n);

            if (op != NULL) {
                if (strcmp(op, "&&") == 0) {
                    if (exit_status == 0 && !ts_node_is_null(right_n))
                        run_single_node(right_n);
                } else if (strcmp(op, "||") == 0) {
                    if (exit_status != 0 && !ts_node_is_null(right_n))
                        run_single_node(right_n);
                } else {
                    if (!ts_node_is_null(right_n)) run_single_node(right_n);
                }
                free(op);
            } else if (!ts_node_is_null(right_n)) {
                run_single_node(right_n);
            }
        }
            
        else if (strcmp(type, "while_statement") == 0) {
            run_while_statement(child);
        }

        else if (strcmp(type, "for_statement") == 0) {
            run_for_statement(child);
        }

        else if (strcmp(type, "do_group") == 0 || strcmp(type, "compound_statement") == 0) {
            run_body(child);
        }

        else{
            printf("node type `%s` not implemented\n", ts_node_type(child));
        }
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

    //store the actual shell's PID
    char shellPID[16];
    snprintf(shellPID,sizeof(shellPID),"%d", getpid());
    hash_put(&shell_vars, "$", shellPID);

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
    DEFINE_FIELD_ID(descriptor);
    DEFINE_FIELD_ID(string_content);

    ts_parser_set_language(parser, bash);

    list_init(&job_list);
    signal_set_handler(SIGCHLD, sigchld_handler);


    /* Read/eval loop. */
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
    return exit_status;
}
