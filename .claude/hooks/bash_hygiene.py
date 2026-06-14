#!/usr/bin/env python3
"""PreToolUse(Bash) hygiene gate for the DNA / LeanEuclidPlus repo.

WHY: CLAUDE.md reserves Bash for read-only git + the `scripts/check_*` / `wire_main` pipeline +
a few path helpers, and says "read files with Read, search with Grep/Glob — never shell out to
cat/head/tail/sed/awk/find/jq/python3 -c". But a *denylist in prose* can't be enforced: an agent
pattern-matches the named commands and invents an unnamed sibling (`python3 -c`, `jq`, `awk`), which
isn't allowlisted either, so it pops a permission prompt for what should just be a Read. This hook
turns the prose rule into a deterministic gate: it DENIES the inspection commands with a message that
names the tool to use instead, and stays silent (falls through to the normal permission flow) for
everything else — so the allowlisted scripts/git/cd keep running exactly as before.

Applies to the main agent AND every subagent (PreToolUse fires for all Bash tool calls).

Contract: read the PreToolUse JSON on stdin; on a blocked command print a deny decision and exit 0;
otherwise print nothing and exit 0 (never block the pipeline by erroring)."""
import sys, json, re, shlex

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

def deny(reason: str):
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PreToolUse",
        "permissionDecision": "deny",
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

        # inline interpreters used for ad-hoc inspection: `python3 -c …`, `python -c …`
        if base in ("python", "python3") and nxt == "-c":
            deny(f"Inline `{base} -c` for inspection is blocked. "
                 f"Read files with Read, search with Grep/Glob, run pipeline checks via "
                 f"scripts/check_*.py. {ALLOWED_SUMMARY}")
        if base in BLOCKED:
            deny(f"`{base}` is blocked for reading/inspection. {BLOCKED[base]} {ALLOWED_SUMMARY}")

    sys.exit(0)

if __name__ == "__main__":
    main()
