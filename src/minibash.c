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
    pid_t pid; /* need to map job to its child process*/
    pid_t pgid; /* need to map job to its child process*/
    int exit_status;//store exit code


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
    /*
    * from the handout:
    * the shell's variable table (shell_vars) is 
    * already initialized in main() as a hashtable 
    * for string -> string
    * for this just use hash_put and assign the 
    * ? variable to the exit_str
    */
    char exit_str[16];
    snprintf(exit_str,sizeof(exit_str), "%d", job->exit_status);
    hash_put(&shell_vars, "?", exit_str);
}


/*
 * Iterate through all possible jobs and check if a job has a PID that matches
 */
static struct job*
find_job_by_pid(pid_t pid){
    //TODO: is iterating through all MAXJOBS the right approach?
    //can we keep track of how many jobs there are from the list?
    
    
    /* Alternative Approch:
     * for(struct list_elem *curr = list_begin(&job_list);
     *      curr != list_end(&job_list);
     *      curr = list_next(curr)){
     *      struct job *currJob = list_entry(curr, struct job, elem);
     *      if(currJob->pid == pid){
     *          return currJob;
     *      }
     *  }
     */
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

    /* To be implemented. 
     * Step 1. Given the pid, determine which job this pid is a part of
     *         (how to do this is not part of the provided code.)
     * Step 2. Determine what status change occurred using the
     *         WIF*() macros.
     * Step 3. Update the job status accordingly, and adjust 
     *         num_processes_alive if appropriate.
     *         If a process was stopped, save the terminal state.
     */



}

static struct job* 
allocate_handler(enum job_status jobStatus){
    //allocate_job
    struct job *thisJob = allocate_job(true);
    thisJob->status = jobStatus;
    thisJob->num_processes_alive = 1;//this might be 0?
    return thisJob;
}


static void strip_quotes_helper(TSNode arg_node,char **argv, int i){
    char *raw = ts_extract_node_text(input, arg_node);
    int len = strlen(raw);
    bool containsDouble = (raw[0] == '"' && raw[len-1] == '"');//starts and ends with double quotes
    bool containsSingle = (raw[0] == '\'' && raw[len-1] == '\'');//stars and ends with single quotes
    if(len >=2 && (containsSingle || containsDouble)){
        argv[i] = strndup(raw+1,len-2);
        free(raw);
    }
    else{
        argv[i] = raw;
    }
}

static const char* shell_variable_helper(char *var_name){
    const char *value = hash_get(&shell_vars, var_name);
    if(value == NULL){//if it wasnt in shell variables...
        value=getenv(var_name);
    }
    //get value from hashtable
    if(value != NULL){
        value =  strdup(value);
        return value;
    }
    return strdup("");
}

static char* command_sub_helper(char **argv){
    //this uses popen(), which takes care of creating pipes
    //forks and running the command
    //it returns a pointer to a file FILE*
    
    char cmd[4096] = {0};//the command itself
    for(int i = 0;argv[i]!=NULL;i++){
        if(i>0){//must add space between the args
            snprintf(cmd + strlen(cmd), sizeof(cmd) - strlen(cmd), "%s", " ");
        }
        snprintf(cmd + strlen(cmd), sizeof(cmd) - strlen(cmd), "%s", argv[i]);
    }

    //open pipes and run
    FILE *fp = popen(cmd, "r");
    if(fp == NULL){
        return strdup("");
    }

    //read output
    char buffer [4096] = {0};
    fread(buffer, 1, sizeof(buffer), fp);

    //remove the new line
    //this is like ex0
    int len = strlen(buffer);
    if(len > 0 && buffer[len-1] == '\n'){
        buffer[len-1] = '\0';
    }

    pclose(fp);
    return strdup(buffer);
}

static char** build_argv(TSNode child){
    int numChild = ts_node_named_child_count(child);
    char **argv = malloc(sizeof(char*) * (numChild+1));//+1 to NULL terminate
                                                       
    //build argv
    for(int i = 0;i<numChild;i++){
        TSNode arg_node = ts_node_named_child(child,i);
        const char *type = ts_node_type(arg_node);

        //this handles echo $? by expanding the variables $ and ?
        if(strcmp(type, "simple_expansion") == 0 || strcmp(type, "expansion") == 0){
            TSNode expansionChild = ts_node_named_child(arg_node, 0);
            char *keyInHT = ts_extract_node_text(input, expansionChild);
            /*
             * variables can be in the system environment or the
             * shell environemtn
             * we gotta check if variables $ are in either
             */

            argv[i] = (char *)shell_variable_helper(keyInHT);
            free(keyInHT);
        }

        //we can prolly call this this quotes handler 
        //maybe make this a helper?
        //bash extracts content without the quotes
        else if(strcmp(type, "string") == 0){
            //get whats inside the double quotes
            char result[4096] = {0};//need an empty string to store the print result
            bool hasContent = false;
            int stringChildren = ts_node_child_count(arg_node);

            for(int j = 0;j<stringChildren;j++){
                TSNode child_node = ts_node_child(arg_node, j);
                const char *type_child = ts_node_type(child_node);
                if(strcmp(type_child, "string_content") == 0){
                    char *content = ts_extract_node_text(input, child_node);
                    snprintf(result + strlen(result), sizeof(result) - strlen(result), "%s", content);
                    free(content);
                    hasContent = true;
                }
                //because shell variables can also be in quotes
                else if(strcmp(type_child, "simple_expansion") == 0 || strcmp(type_child, "expansion") == 0){
                    TSNode expansionChild = ts_node_named_child(child_node, 0);
                    char *keyInHT = ts_extract_node_text(input, expansionChild);
                    char *expanded = (char*)shell_variable_helper(keyInHT);
                    snprintf(result + strlen(result), sizeof(result) - strlen(result), "%s", expanded);
                    /*
                     * variables can be in the system environment or the
                     * shell environemtn
                     * we gotta check if variables $ are in either
                     */

                    free(keyInHT);
                    free(expanded);
                    hasContent = true;
                }
            }
            if(!hasContent){
                //empty strjng "" case
                strip_quotes_helper(arg_node, argv, i);
                //this logic is now in this helper^^
                // char *raw = ts_extract_node_text(input, arg_node);
                // int len = strlen(raw);
                // if(len >=2 && raw[0] == '"' && raw[len-1] == '"'){
                //     argv[i] = strndup(raw+1,len-2);
                //     free(raw);
                // }
                // else{
                //     argv[i] = raw;
                // }
            }else{
                argv[i] = strdup(result);
            }
        }
        // for some reason the tree sitter calls single quotes "raw strings"
        else if(strcmp(type, "raw_string") == 0){
            //strip the single quotes
            strip_quotes_helper(arg_node, argv, i);
            //this logic is now in this helper^^
            // char *raw = ts_extract_node_text(input, arg_node);
            // int len = strlen(raw);
            // if(len >=2 && raw[0] == '\'' && raw[len-1] == '\''){
            //     argv[i] = strndup(raw+1,len-2);
            //     free(raw);
            // }
            // else{
            //     argv[i] = raw;
            // }
        }

        else if(strcmp(type, "command_substitution") == 0){
            TSNode inner_cmd = ts_node_named_child(arg_node, 0);
            char **inner_argv = build_argv(inner_cmd);//yes, recursion

            //free the inner arg commands
            argv[i] = command_sub_helper(inner_argv);
            for(int j = 0;inner_argv[j] != NULL;j++){
                free(inner_argv[j]);
            }
            free(inner_argv);

        }
        //regulr word, no quotes
        else{
            argv[i] = ts_extract_node_text(input, arg_node);
        }
    }
    argv[numChild] = NULL;//null terminate for posix_spawnp
    return argv;
}


static void free_argv(char **argv, int numChild){
    for(int i = 0;i<numChild;i++){
        free(argv[i]);//free text returned by ts_extract_node_text
    }
    free(argv);//free from malloc^^^^
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
            //PIPES
            uint32_t numChild = ts_node_named_child_count(child);

            struct job *thisJob = allocate_handler(FOREGROUND); 
            thisJob -> num_processes_alive = 0;
            thisJob->pgid = 0;

            int stdin_fd = STDIN_FILENO;//first command (ls) must read from stdin


            //ls | cat 
            //stdout of ls goes into stdin vim 
            for(int i = 0;i<numChild;i++){
                TSNode currNode = ts_node_named_child(child,i);

                //build argv for each command between | pipes
                char **argv = build_argv(currNode);
                int pipe[2];
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
                if (i != numChild-1){
                    posix_spawn_file_actions_adddup2(&actions, pipe[1], STDOUT_FILENO);
                }

                posix_spawnattr_t attrs;
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

        }// 
        else if(strcmp(type, "redirected_statement") == 0){
            //get the body of the node
            TSNode bodyNode = ts_node_child_by_field_id(child, bodyId);
            char **argv = build_argv(bodyNode);
            int argc = ts_node_named_child_count(bodyNode);

            //start actions like from piping
            posix_spawn_file_actions_t actions;
            posix_spawn_file_actions_init(&actions);

            //count how many redirects
            int redirects = ts_node_named_child_count(child);
            int fds[16];
            int num_fds_open = 0;
            for(int i = 0;i<redirects;i++){
                //child in "ls > out.txt" is: "> out.txt"
                TSNode redirect_child = ts_node_named_child(child, i);
                const char *typeShi = ts_node_type(redirect_child);//why typeShi? bc type was taken

                //need this loop for multiple file redirects in a single command: ls > yo.txt > wc
                if(strcmp(typeShi, "file_redirect") == 0){
                    TSNode destination = ts_node_child_by_field_id(redirect_child, destinationId);
                    char *filename = ts_extract_node_text(input, destination);
                    char *redir_text = ts_extract_node_text(input, redirect_child);

                    //check if the redicret has a file descriptor
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
                    }
                    else if(strncmp(redir_text,">&",2) == 0  || strncmp(redir_text,"2>&",3) == 0){
                        // >&N or 2>&N means fd to fd
                        target_fd = source_fd;
                        skip_open = true;
                    }
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
                        posix_spawn_file_actions_adddup2(&actions,dest_fd,target_fd);
                    }
                    else if(strncmp(redir_text, "&>", 2) == 0){
                        //this is the case for &>, open file and then must dup2 
                        //TWICE for both STDOUT AND STDERR!!!
                        int fd = open(filename, flags, 0666);
                        if (fd == -1){
                            printf("open failed");
                        }
                        else{
                            posix_spawn_file_actions_adddup2(&actions, fd, STDOUT_FILENO);
                            posix_spawn_file_actions_adddup2(&actions, fd, STDERR_FILENO);
                            fds[num_fds_open++] = fd;
                        }

                    }
                    else if( target_fd != -1){
                        int fd = open(filename, flags, 0666);
                        if (fd == -1){
                            printf("open failed");
                        }
                        else{
                            posix_spawn_file_actions_adddup2(&actions, fd, target_fd);
                            fds[num_fds_open++] = fd;
                        }
                    }

                    //cleanup
                    free(filename);
                    free(redir_text);
                }
            }

            //create the job
            struct job *thisJob = allocate_handler(FOREGROUND);
            thisJob->num_processes_alive = 0;

            int pid;
            int result = posix_spawnp(&pid, argv[0], &actions, NULL, argv, environ);

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
        }
        
        else if(strcmp(type, "variable_assignment") == 0){
            //its getting repetitive asf now....
            //getting it from the index
            TSNode varAssign_name = ts_node_named_child(child, 0);
            TSNode varAssign_value= ts_node_named_child(child, 1);

            //get the name and value from the TSNode
            char *var_name = ts_extract_node_text(input, varAssign_name);
            char *var_value = ts_extract_node_text(input, varAssign_value);

            //put in in the given hastable shell_vars
            hash_put(&shell_vars, var_name, var_value);

            free(var_name);
            free(var_value);
            //notice no allocation of job here
            //
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
