#!/usr/bin/env python3
"""PreToolUse(Bash) hygiene gate for the DNA / LeanEuclidPlus repo.

WHY: CLAUDE.md reserves Bash for read-only git + the `scripts/check_*` / `wire_main` pipeline +
a few path helpers, and says "read files with Read, search with Grep/Glob — never shell out to
cat/head/tail/sed/awk/find/jq/python3 -c". But a *denylist in prose* can't be enforced: an agent
pattern-matches the named commands and invents an unnamed sibling (`python3 -c`, `jq`, `awk`, or a
git SUBcommand like `git grep` that isn't a leading `grep` token at all), which isn't allowlisted
either, so it falls through this hook AND has no settings.json allow match, popping a normal
permission prompt for what should've been silently gated. This hook is a POSITIVE allowlist gate,
not a denylist of named-bad commands: every sub-command is checked against the known-good shapes
(read-only git, the pipeline scripts, the path helpers) and anything that doesn't match — including
unnamed siblings and git/lake subcommands outside the allowed set — is gated the same way as the
explicitly-named inspection binaries.

The gate's reaction to an off-allowlist command is set by `hygiene.conf` (read fresh every run, so an
edit takes effect on the very next command):
  mode = ask    -> pause and PROMPT the user to approve/reject it          (default; "go through me")
  mode = deny   -> hard-block it silently, naming the right tool            ("don't bug me")
This is the "sometimes block, sometimes let me decide" knob: flip one word in hygiene.conf. ("just run
everything" is not a mode here — that's settings.json's Bash() allowlist, not this hygiene gate.)

Applies to the main agent AND every subagent (PreToolUse fires for all Bash tool calls).

Contract: read the PreToolUse JSON on stdin; on an off-allowlist command print the configured
decision (ask/deny) and exit 0, or nothing for allow; otherwise print nothing and exit 0 (never
block the pipeline by erroring)."""
import sys, json, re, shlex, os

# binary basename -> what to do instead (shown to the model on deny). The Grep/Glob TOOLS do NOT exist
# in this harness, so the old "use the Grep/Glob tool" redirects were dead ends — read-only inspection
# binaries are now ALLOWED (see READONLY_OK). Only genuine in-place transformers stay blocked.
BLOCKED = {
    "sed":   "Read with the Read tool, or change a file with the Edit tool — not sed (sed -i mutates).",
    "awk":   "Read with the Read tool, or search with grep — not awk (awk can transform in place).",
    "jq":    "Read the JSON file with the Read tool (or, for the pipeline, run scripts/check_*.py).",
}

# Read-only inspection binaries — ALLOWED to run bare. The dedicated Grep/Glob tools are NOT available
# in this deployment, so these ARE how the agent searches/reads via bash; settings.json also allows them
# so they never prompt. CAVEAT (accepted): shell redirection (`grep x > out`) or `find … -delete/-exec`
# can still mutate — treated as read-only here; git is the human's safety net for those edge cases.
READONLY_OK = {"cat", "head", "tail", "wc", "find", "grep", "egrep", "fgrep", "rg", "ls"}

# The positive allowlist, echoed in every deny message so the agent learns the boundary once.
ALLOWED_SUMMARY = ("Bash here is reserved for: read-only git (status/diff/log/show/branch/blame/"
                   "ls-files), python3 scripts/check_*.py, scripts/check_faithful.sh, "
                   "python3 scripts/wire_main.py, python3 scripts/find.py, "
                   "python3 scripts/bake_index.py, python3 scripts/scaffold_step.py, "
                   "python3 scripts/faithful_map_assemble.py, python3 -m pytest, "
                   "lake env/exe, cd/pwd/mkdir, and read-only inspection "
                   "(grep/rg/find/cat/head/tail/ls/wc). "
                   "Read files with the Read tool; find.py is the sanctioned smart-grep over the "
                   "System-E declaration database. (The Grep/Glob TOOLS are not available in this "
                   "harness — use bash grep/find or the Read tool.)")

_CONF = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hygiene.conf")

def read_mode() -> str:
    """Off-list-command policy, re-read every run so edits take effect on the next command.
    'ask' (default) force-prompts the user; 'deny' hard-blocks silently."""
    try:
        with open(_CONF) as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                m = re.match(r"mode\s*=\s*(\w+)", line)
                if m:
                    v = m.group(1).lower()
                    return v if v in ("ask", "deny") else "ask"
    except Exception:
        pass
    return "ask"

def gate(reason: str):
    """Block an off-allowlist command per the configured mode (ask force-prompts, deny silences)."""
    decision = "deny" if read_mode() == "deny" else "ask"
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PreToolUse",
        "permissionDecision": decision,
        "permissionDecisionReason": reason,
    }}))
    sys.exit(0)

# git subcommands considered read-only / always fine (mirrors settings.json's allow list).
GIT_READONLY = {"status", "diff", "log", "show", "branch", "ls-files", "blame"}
# bases that are fine with any arguments (mirrors settings.json's :* allow entries).
BARE_OK = {"realpath", "dirname", "basename", "mkdir", "echo", "pwd", "cd"}

def _segments(cmd):
    """Split a command line into sub-command token-lists at top-level shell operators (| || && ; &),
    RESPECTING quotes — so a `|` inside `grep -E 'a|b'` (or an alternation regex `(png|txt)`) is NOT
    treated as a separator. The old naive `re.split(r'\\|', cmd)` shredded such greps into fake commands
    ('txt)', 'Prop14', …) and wrongly blocked them now that grep/find are allowed. Falls back to one
    naive segment on a lex error (e.g. unbalanced quotes) — safe (won't mis-split)."""
    try:
        lex = shlex.shlex(cmd, posix=True, punctuation_chars="|&;")
        lex.whitespace_split = True
        lex.commenters = ""
        toks = list(lex)
    except ValueError:
        return [cmd.split()]
    segs, cur = [], []
    for t in toks:
        if t and all(c in "|&;" for c in t):        # a run of unquoted shell separators (| || && ; …)
            if cur:
                segs.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:
        segs.append(cur)
    return segs


def main():
    try:
        data = json.load(sys.stdin)
    except Exception:
        sys.exit(0)  # unparseable input: never block
    cmd = ((data.get("tool_input") or {}).get("command") or "")
    if not cmd.strip():
        sys.exit(0)

    # Inspect every sub-command (split on shell separators) against a POSITIVE allowlist — anything
    # that doesn't match a known-good shape is gated (ask/deny per hygiene.conf), not just the named
    # inspection binaries. This is what catches `git grep` (a git SUBcommand, not a leading `grep`),
    # `git fetch`, `npm install`, etc. — anything CLAUDE.md's allowlist doesn't name.
    for toks in _segments(cmd):
        if not toks:
            continue
        # skip leading ENV=val assignments and a leading 'command'/'builtin' wrapper
        i = 0
        while i < len(toks) and (re.match(r"^[A-Za-z_][A-Za-z0-9_]*=", toks[i])
                                 or toks[i] in ("command", "builtin", "exec", "time", "nohup")):
            i += 1
        if i >= len(toks):
            continue
        base = toks[i].rsplit("/", 1)[-1]
        nxt = toks[i + 1] if i + 1 < len(toks) else ""
        nxt2 = toks[i + 2] if i + 2 < len(toks) else ""

        # Read-only inspection binaries run bare (Grep/Glob tools don't exist here — this is search).
        if base in READONLY_OK:
            continue

        # Genuine in-place transformers still get a specific "use this tool instead" message.
        if base in BLOCKED:
            gate(f"`{base}` is blocked for reading/inspection. {BLOCKED[base]} {ALLOWED_SUMMARY}")

        # python/python3: ALLOWLIST, not denylist — the only sanctioned python here is running a
        # pipeline script (`python3 scripts/check_*.py …` / `scripts/wire_main.py …`). EVERYTHING else
        # — `-c`, a stdin heredoc (`python3 - <<EOF`), a process-sub (`python3 <(…)`), or an ad-hoc
        # `python3 some_scratch.py` — is ad-hoc code execution for inspection and is gated.
        if base in ("python", "python3"):
            arg = nxt.rsplit("/", 1)[-1]
            ok = (nxt.startswith("scripts/") or nxt.startswith("./scripts/")) and (
                arg.startswith("check_") or arg in ("wire_main.py", "smt_probe.py",
                                                    "find.py", "bake_index.py", "scaffold_step.py",
                                                     "faithful_map_assemble.py", "assumptions.py"))

            # also allow running the parse-only test suite bare: `python3 -m pytest tests/…`
            if not ok and nxt == "-m" and nxt2 == "pytest":
                ok = True
            if not ok:
                gate(f"`{base}` here may ONLY run the pipeline scripts "
                     f"(`python3 scripts/check_step.py …` / `check_steps.py` / `check_faithful.py` / "
                     f"`check_signatures.py` / `wire_main.py`). Inline code (`-c`), a stdin heredoc "
                     f"(`python3 - <<EOF`), a process-substitution, or an ad-hoc script is blocked — "
                     f"read files with the Read tool, search with Grep/Glob. {ALLOWED_SUMMARY}")
            # INTEGRITY GATE — always hard-deny, independent of hygiene.conf's ask/deny knob:
            # `--save` rewrites the human-approved signature baselines (scripts/{step,proposition}_
            # signatures.json). That is a HUMAN-only action at the Phase-A gate; the AI may run
            # these scripts in check mode only. (settings.json globs can't enforce this —
            # settings.local.json's broad `Bash(python3 *)` allow makes arg-specific denies
            # bypassable by reformulation; this shlex'd token check is the airtight point.)
            if arg in ("check_steps.py", "check_signatures.py") and "--save" in toks:
                print(json.dumps({"hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "deny",
                    "permissionDecisionReason":
                        "`--save` rewrites the approved signature baseline "
                        "(scripts/step_signatures.json / proposition_signatures.json) — a human-only "
                        "action at the Phase-A gate. Run these scripts in check mode (no --save). "
                        f"{ALLOWED_SUMMARY}",
                }}))
                sys.exit(0)
            continue  # ok: a sanctioned pipeline-script invocation

        if base in BARE_OK:
            continue

        if base == "lake":
            if nxt == "env":
                continue
            if nxt == "exe" and nxt2.rsplit("/", 1)[-1] == "faithful_export":
                continue
            gate(f"`lake {nxt}` is not on the allowlist (only `lake env` / `lake exe "
                 f"faithful_export` are). {ALLOWED_SUMMARY}")

        if base == "git":
            if nxt in GIT_READONLY:
                continue
            gate(f"`git {nxt}` is not on the read-only git allowlist "
                 f"(status/diff/log/show/branch/blame/ls-files) — e.g. `git grep` should be the Grep "
                 f"tool, not a shelled-out git subcommand. {ALLOWED_SUMMARY}")

        if base == "check_faithful.sh":
            continue

        if base == "rm":
            # Scoped delete: agents MAY remove files inside a prop folder (Book<N>/Prop<NN>/…) — their
            # own workspace, with git as the safety net (they can't git, the human commits). Anything
            # else — flat originals (Book/PropNN.lean), SystemE, scripts, whole trees, an absolute path,
            # or a `..` escape — is HARD-DENIED regardless of the ask/deny knob.
            targets = [t for t in toks[i + 1:] if not t.startswith("-")]
            prop_re = re.compile(r"(^|/)Book\d+/Prop\d+(/|$)")
            safe = bool(targets) and all(
                prop_re.search(t) and ".." not in t.split("/") and not t.startswith("/")
                for t in targets)
            if safe:
                continue
            print(json.dumps({"hookSpecificOutput": {
                "hookEventName": "PreToolUse",
                "permissionDecision": "deny",
                "permissionDecisionReason":
                    "`rm` here may ONLY target files inside a prop folder (Book<N>/Prop<NN>/…) — the "
                    "agent's own workspace, with git as the safety net. Deleting a flat original, "
                    "SystemE, scripts, a whole tree, or anything via an absolute path or `..` is "
                    "blocked. " + ALLOWED_SUMMARY,
            }}))
            sys.exit(0)

        # Anything else entirely unrecognized — not a denylisted inspection binary, not python, not
        # one of the path helpers, not a read-only git/lake/pipeline-script invocation.
        gate(f"`{base}` is not on the Bash allowlist here. {ALLOWED_SUMMARY}")

    sys.exit(0)

if __name__ == "__main__":
    main()
