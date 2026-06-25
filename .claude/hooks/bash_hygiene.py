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

# binary basename -> what to do instead (shown to the model on deny)
BLOCKED = {
    "cat":   "Read the file with the Read tool.",
    "head":  "Read the file with the Read tool (use the offset/limit args for a slice).",
    "tail":  "Read the file with the Read tool (use the offset/limit args for a slice).",
    "sed":   "Read with the Read tool, or change a file with the Edit tool — not sed.",
    "awk":   "Read with the Read tool / search with the Grep tool — not awk.",
    "jq":    "Read the JSON file with the Read tool (or, for the pipeline, run scripts/check_*.py).",
    "wc":    "Read the file with the Read tool; raw line counts aren't part of the proving loop.",
    "find":  "Find files with the Glob tool.",
    "grep":  "Search with the Grep tool.",
    "egrep": "Search with the Grep tool.",
    "fgrep": "Search with the Grep tool.",
    "rg":    "Search with the Grep tool.",
    "ls":    "List/inspect with the Glob tool (e.g. 'DIR/*').",
}

# The positive allowlist, echoed in every deny message so the agent learns the boundary once.
ALLOWED_SUMMARY = ("Bash here is reserved for: read-only git (status/diff/log/show/branch/blame/"
                   "ls-files), python3 scripts/check_*.py, scripts/check_faithful.sh, "
                   "python3 scripts/wire_main.py, python3 scripts/find.py, "
                   "python3 scripts/bake_index.py, python3 scripts/scaffold_step.py, python3 -m pytest, "
                   "lake env/exe, and cd/pwd/mkdir. "
                   "For everything else use the Read / Grep / Glob tools (find.py is the sanctioned "
                   "smart-grep over the System-E declaration database).")

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
    for seg in re.split(r"&&|\|\||\||;|\n", cmd):
        seg = seg.strip()
        if not seg:
            continue
        try:
            toks = shlex.split(seg)
        except ValueError:
            toks = seg.split()
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

        # Known-bad inspection binaries get a specific "use this tool instead" message.
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
                                                    "find.py", "bake_index.py", "scaffold_step.py"))
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

        # Anything else entirely unrecognized — not a denylisted inspection binary, not python, not
        # one of the path helpers, not a read-only git/lake/pipeline-script invocation.
        gate(f"`{base}` is not on the Bash allowlist here. {ALLOWED_SUMMARY}")

    sys.exit(0)

if __name__ == "__main__":
    main()
