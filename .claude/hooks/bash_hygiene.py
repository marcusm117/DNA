#!/usr/bin/env python3
"""PreToolUse(Bash) hygiene gate for the DNA / LeanEuclidPlus repo.

WHY: CLAUDE.md reserves Bash for read-only git + the `scripts/check_*` / `wire_main` pipeline +
a few path helpers, and says "read files with Read, search with Grep/Glob — never shell out to
cat/head/tail/sed/awk/find/jq/python3 -c". But a *denylist in prose* can't be enforced: an agent
pattern-matches the named commands and invents an unnamed sibling (`python3 -c`, `jq`, `awk`), which
isn't allowlisted either, so it pops a permission prompt for what should just be a Read. This hook
turns the prose rule into a deterministic gate on the inspection commands, with a message that names
the tool to use instead; allowlisted scripts/git/cd fall through silently and keep running as before.

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
                   "python3 scripts/wire_main.py, lake env/exe, and cd/pwd/mkdir. "
                   "For everything else use the Read / Grep / Glob tools.")

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

def main():
    try:
        data = json.load(sys.stdin)
    except Exception:
        sys.exit(0)  # unparseable input: never block
    cmd = ((data.get("tool_input") or {}).get("command") or "")
    if not cmd.strip():
        sys.exit(0)

    # Inspect every sub-command (split on shell separators), so a blocked binary anywhere in a
    # pipeline/chain is caught — including the "scripts/check_step.py … | grep …" anti-pattern.
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

        # python/python3: ALLOWLIST, not denylist — the only sanctioned python here is running a
        # pipeline script (`python3 scripts/check_*.py …` / `scripts/wire_main.py …`). EVERYTHING else
        # — `-c`, a stdin heredoc (`python3 - <<EOF`), a process-sub (`python3 <(…)`), or an ad-hoc
        # `python3 some_scratch.py` — is ad-hoc code execution for inspection and is DENIED. (This is
        # what closes the `python3 -c` *and* the `python3 -`/heredoc holes at once.)
        if base in ("python", "python3"):
            arg = nxt.rsplit("/", 1)[-1]
            ok = (nxt.startswith("scripts/") or nxt.startswith("./scripts/")) and (
                arg.startswith("check_") or arg in ("wire_main.py", "smt_probe.py"))
            if not ok:
                gate(f"`{base}` here may ONLY run the pipeline scripts "
                     f"(`python3 scripts/check_step.py …` / `check_steps.py` / `check_faithful.py` / "
                     f"`check_signatures.py` / `wire_main.py`). Inline code (`-c`), a stdin heredoc "
                     f"(`python3 - <<EOF`), a process-substitution, or an ad-hoc script is blocked — "
                     f"read files with the Read tool, search with Grep/Glob. {ALLOWED_SUMMARY}")
        if base in BLOCKED:
            gate(f"`{base}` is blocked for reading/inspection. {BLOCKED[base]} {ALLOWED_SUMMARY}")

    sys.exit(0)

if __name__ == "__main__":
    main()
