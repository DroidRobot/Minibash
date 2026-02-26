# Minibash Implementation Plan

## Current Status (as of latest push)

### Passing tests (43/70 basic points)
001-comment, 005-command, 007-command, 010-command-with-args,
015-command-with-quoted-args, 020-exit-status-var, 022-exit-status-on-crash,
025-sh-pid-var, 032-variable, 040-command-expansion-1, 050-pipeline-1,
060-pipeline-redirect1, 064-pipeline-redirect-stderr

### Failing tests and root causes

#### 030-variable-env / 033-variable-quote
**Cause:** Environment issue. The test runner (`minibash_driver.py`) does not set
`LANG=en_US.UTF-8`. These tests pass on rlogin where LANG is set. No code change
needed for this machine — your code correctly handles `$LANG` and `${LANG}`.

#### 070-lists-1 / 071-lists-2
**Cause:** `list` AST node type (&&, ||) is not handled. When bash sees
`false && echo foo || echo bar`, tree-sitter produces a `list` node with
`left`, `operator`, and `right` fields. Your `run_program` falls through to
the `else` branch printing "node type `list` not implemented".

#### 080-command-expansion-with-pipe
**Cause:** `build_argv` handles `command_substitution` by recursively calling
`build_argv(inner_cmd)` where `inner_cmd` is the first named child. For
`$(echo dlroW | rev)`, that child is a `pipeline` node. `build_argv` on a
`pipeline` returns the entire command nodes as text (["echo dlroW", "rev"]),
so `command_sub_helper` runs `echo dlroW rev` → wrong output.

#### 090-095 if statements / 100-104 for loops / 200-201 while loops
**Cause:** These node types are not implemented. Also, `variable_assignment`
only extracts raw text, so `count=$(expr $count + 1)` stores the literal
string `$(expr $count + 1)` instead of running the command.

---

## Implementation Steps

### Step 1 — Fix command substitution with pipeline (fixes test 080)

In `build_argv`, find the `command_substitution` branch and replace the
recursive `build_argv` approach with direct text extraction + popen:

```c
else if(strcmp(type, "command_substitution") == 0) {
    // Extract the text between $( and ) and run it via /bin/sh
    // This handles pipelines, builtins, and everything else correctly.
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
}
```

`ts_extract_node_text_from_to(input, node, 2, 1)` trims `$(` from the start
and `)` from the end, giving the raw shell command text. `popen` runs it via
`/bin/sh -c`, which handles pipelines natively.

---

### Step 2 — Add `last_exit_status` global and update wait_for_job

Add at the top of the file (near `shouldexit`):
```c
static int last_exit_status = 0;
```

Inside `wait_for_job`, after the `hash_put`:
```c
last_exit_status = job->exit_status;
```

This global is checked by list (&&/||) logic and by if/while conditions.

---

### Step 3 — Add `exec_exception` for break/continue

Add at the top:
```c
typedef enum {
    EXEC_NORMAL   = 0,
    EXEC_BREAK    = 1,
    EXEC_CONTINUE = 2
} exec_exception_t;
static exec_exception_t exec_exception = EXEC_NORMAL;
```

---

### Step 4 — Add `expand_value` helper

This function expands a value-type AST node (command_substitution,
simple_expansion, expansion, string, raw_string, word, concatenation) to a
heap-allocated string. Used for variable assignments and for-loop values.

```c
static char *expand_value(TSNode node) {
    if (ts_node_is_null(node)) return strdup("");
    const char *type = ts_node_type(node);

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
    if (strcmp(type, "simple_expansion") == 0 || strcmp(type, "expansion") == 0) {
        TSNode var_node = ts_node_named_child(node, 0);
        char *varname = ts_extract_node_text(input, var_node);
        char *result = (char *)shell_variable_helper(varname);
        free(varname);
        return result;
    }
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
            } else if (strcmp(ct, "simple_expansion") == 0 || strcmp(ct, "expansion") == 0) {
                TSNode vn = ts_node_named_child(cn, 0);
                char *vname = ts_extract_node_text(input, vn);
                char *val = (char *)shell_variable_helper(vname);
                strncat(result, val, sizeof(result) - strlen(result) - 1);
                free(vname); free(val);
            } else if (strcmp(ct, "command_substitution") == 0) {
                char *sub = expand_value(cn);
                strncat(result, sub, sizeof(result) - strlen(result) - 1);
                free(sub);
            }
        }
        return strdup(result);
    }
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
    // word, number, etc.
    return ts_extract_node_text(input, node);
}
```

---

### Step 5 — Fix `variable_assignment` to use `expand_value`

Replace the current assignment handler with:
```c
else if (strcmp(type, "variable_assignment") == 0) {
    TSNode varAssign_name  = ts_node_named_child(child, 0);
    TSNode varAssign_value = ts_node_named_child(child, 1);
    char *var_name  = ts_extract_node_text(input, varAssign_name);
    char *var_value = ts_node_is_null(varAssign_value)
                      ? strdup("")
                      : expand_value(varAssign_value);
    hash_put(&shell_vars, var_name, var_value);
    free(var_name);
    free(var_value);
}
```

---

### Step 6 — Refactor `run_program` into `execute_statement` + add list/if/while/for

**Forward declarations to add (before pipeline_helper):**
```c
static void execute_statement(TSNode child);
```

**Add `run_body` (executes named children of a body node like do_group):**
```c
static void run_body(TSNode body_node) {
    if (ts_node_is_null(body_node)) return;
    uint32_t nc = ts_node_named_child_count(body_node);
    for (uint32_t i = 0; i < nc; i++) {
        if (exec_exception != EXEC_NORMAL) break;
        execute_statement(ts_node_named_child(body_node, i));
    }
}
```

**Add `execute_condition` (runs a node and returns its exit status):**
```c
static int execute_condition(TSNode cond_node) {
    if (ts_node_is_null(cond_node)) return 0;
    execute_statement(cond_node);
    return last_exit_status;
}
```

**Add `run_if_statement`:**
```c
static void run_if_statement(TSNode node) {
    TSNode cond = ts_node_child_by_field_id(node, conditionId);
    TSNode body = ts_node_child_by_field_id(node, bodyId);

    if (execute_condition(cond) == 0) { run_body(body); return; }

    uint32_t nc = ts_node_named_child_count(node);
    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_named_child(node, i);
        const char *ct = ts_node_type(child);
        if (strcmp(ct, "elif_clause") == 0) {
            TSNode ec = ts_node_child_by_field_id(child, conditionId);
            TSNode eb = ts_node_child_by_field_id(child, bodyId);
            if (execute_condition(ec) == 0) { run_body(eb); return; }
        } else if (strcmp(ct, "else_clause") == 0) {
            TSNode eb = ts_node_child_by_field_id(child, bodyId);
            run_body(eb); return;
        }
    }
}
```

**Add `run_while_statement`:**
```c
static void run_while_statement(TSNode node) {
    TSNode cond = ts_node_child_by_field_id(node, conditionId);
    TSNode body = ts_node_child_by_field_id(node, bodyId);
    for (;;) {
        if (execute_condition(cond) != 0) break;
        run_body(body);
        if (exec_exception == EXEC_BREAK)    { exec_exception = EXEC_NORMAL; break; }
        if (exec_exception == EXEC_CONTINUE) { exec_exception = EXEC_NORMAL; continue; }
    }
}
```

**Add `run_for_statement`:**
```c
static void run_for_statement(TSNode node) {
    TSNode var_node = ts_node_child_by_field_id(node, variableId);
    TSNode body     = ts_node_child_by_field_id(node, bodyId);
    if (ts_node_is_null(var_node)) return;
    char *varname = ts_extract_node_text(input, var_node);

    uint32_t nc = ts_node_named_child_count(node);
    char **values = malloc(nc * sizeof(char *));
    int nvalues = 0;
    for (uint32_t i = 0; i < nc; i++) {
        TSNode child = ts_node_named_child(node, i);
        const char *ct = ts_node_type(child);
        if (child.id == var_node.id) continue;
        if (!ts_node_is_null(body) && child.id == body.id) continue;
        if (strcmp(ct, "do_group") == 0) continue;
        values[nvalues++] = expand_value(child);
    }

    for (int i = 0; i < nvalues; i++) {
        if (exec_exception != EXEC_NORMAL) break;
        hash_put(&shell_vars, varname, values[i]);
        run_body(body);
        if (exec_exception == EXEC_BREAK)    { exec_exception = EXEC_NORMAL; break; }
        if (exec_exception == EXEC_CONTINUE) { exec_exception = EXEC_NORMAL; continue; }
    }
    for (int i = 0; i < nvalues; i++) free(values[i]);
    free(values);
    free(varname);
}
```

**Rewrite `execute_statement` (replacing run_program's if-else chain):**

`execute_statement` handles ALL node types. `run_program` becomes a thin wrapper:

```c
static void execute_statement(TSNode child) {
    const char *type = ts_node_type(child);

    if (strcmp(type, "comment") == 0) return;

    else if (strcmp(type, "command") == 0) {
        /* ... same code as current run_program command case ... */
        /* But add: handle "break" and "continue" builtins */
        /* And at end set: last_exit_status from job */
    }
    else if (strcmp(type, "pipeline") == 0) {
        pipeline_helper(child, NULL, NULL, 0);
        /* last_exit_status already set inside wait_for_job */
    }
    else if (strcmp(type, "redirected_statement") == 0) {
        /* ... same as current run_program redirected_statement case ... */
    }
    else if (strcmp(type, "variable_assignment") == 0) {
        /* use expand_value for the value */
    }
    else if (strcmp(type, "list") == 0) {
        TSNode left  = ts_node_child_by_field_id(child, leftId);
        TSNode op_n  = ts_node_child_by_field_id(child, operatorId);
        TSNode right = ts_node_child_by_field_id(child, rightId);
        if (!ts_node_is_null(left)) execute_statement(left);
        if (!ts_node_is_null(op_n)) {
            char *op = ts_extract_node_text(input, op_n);
            if (strcmp(op, "&&") == 0) {
                if (last_exit_status == 0 && !ts_node_is_null(right))
                    execute_statement(right);
            } else if (strcmp(op, "||") == 0) {
                if (last_exit_status != 0 && !ts_node_is_null(right))
                    execute_statement(right);
            } else {
                if (!ts_node_is_null(right)) execute_statement(right);
            }
            free(op);
        }
    }
    else if (strcmp(type, "if_statement") == 0)    run_if_statement(child);
    else if (strcmp(type, "while_statement") == 0) run_while_statement(child);
    else if (strcmp(type, "for_statement") == 0)   run_for_statement(child);
    else if (strcmp(type, "do_group") == 0 ||
             strcmp(type, "compound_statement") == 0) run_body(child);
    else {
        printf("node type `%s` not implemented\n", type);
    }
}

static void run_program(TSNode program) {
    uint32_t count = ts_node_named_child_count(program);
    for (uint32_t i = 0; i < count; i++) {
        if (exec_exception != EXEC_NORMAL) break;
        execute_statement(ts_node_named_child(program, i));
    }
}
```

---

### Step 7 — Add `break` and `continue` builtins in the command handler

Inside the `command` case in `execute_statement`, before calling `posix_spawnp`:
```c
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
```

---

### Step 8 — Update `run_program` to check `exec_exception`

Already done in Step 6: check `exec_exception != EXEC_NORMAL` at the start of
each loop iteration and break early.

---

## Test Coverage After Fixes

| Test | Fix |
|------|-----|
| 070-lists-1 | Step 6: list node (&&/||) |
| 071-lists-2 | Step 6: list node (&&/||) |
| 080-cmd-expansion-with-pipe | Step 1: cmd substitution fix |
| 090-095 if statements | Step 6: if_statement |
| 100-for-loop-1 | Step 6: for_statement |
| 104-for-loop-break | Steps 6+7: for + break builtin |
| 200-while-complex | Steps 5+6: expand_value + while |
| 201-while-complex-2 | Steps 5+6: expand_value + while |
