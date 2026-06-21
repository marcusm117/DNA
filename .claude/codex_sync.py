#!/usr/bin/env python3
"""One-off: symlink this repo's .claude/ config into Codex CLI's equivalent
locations, so Claude's files stay the single source of truth. See
/u/taddmao/.claude/plans/ok-sure-let-s-do-agile-zebra.md for the full plan.

Phase A only: skills -> <repo>/.agents/skills/<name> (repo-scoped -- verified
via a throwaway probe that this is visible inside the repo and NOT outside
it; ~/.codex/skills is the GLOBAL/all-projects location and must not be used
for project-specific skills), CLAUDE.md -> AGENTS.md.
Safe to re-run (idempotent; never overwrites a non-symlink or a symlink
pointing somewhere else without saying so first).
"""
import os
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SKILLS_SRC = os.path.join(REPO_ROOT, ".claude", "skills")
CODEX_SKILLS_DIR = os.path.join(REPO_ROOT, ".agents", "skills")


def ensure_symlink(link_path, target_path, label):
    target_path = os.path.abspath(target_path)
    if os.path.islink(link_path):
        existing = os.path.realpath(link_path)
        if existing == os.path.realpath(target_path):
            print(f"OK    {label}: already linked correctly")
            return
        print(f"SKIP  {label}: existing symlink points elsewhere ({existing}) -- not touching")
        return
    if os.path.exists(link_path):
        print(f"SKIP  {label}: {link_path} exists and is not a symlink -- not touching")
        return
    os.makedirs(os.path.dirname(link_path), exist_ok=True)
    os.symlink(target_path, link_path)
    print(f"LINK  {label}: {link_path} -> {target_path}")


def main():
    if not os.path.isdir(SKILLS_SRC):
        sys.exit(f"no skills dir at {SKILLS_SRC}")

    for name in sorted(os.listdir(SKILLS_SRC)):
        src = os.path.join(SKILLS_SRC, name)
        if not os.path.isdir(src):
            continue
        ensure_symlink(os.path.join(CODEX_SKILLS_DIR, name), src, f"skill '{name}'")

    ensure_symlink(
        os.path.join(REPO_ROOT, "AGENTS.md"),
        os.path.join(REPO_ROOT, "CLAUDE.md"),
        "AGENTS.md -> CLAUDE.md",
    )


if __name__ == "__main__":
    main()
