"""pytest config for the parse-only tooling tests (bake_index / find / faithful_lib parse helpers).

Puts `scripts/` on sys.path so the tests can `import faithful_lib`, `bake_index`, `find` exactly as
the scripts import each other. These tests are PURE PARSE — no Lean, no `lake`, no SMT — so they run
in milliseconds and need no build environment. Run from LeanEuclidPlus/:  python3 -m pytest tests/
"""
import os
import sys

SCRIPTS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts")
sys.path.insert(0, SCRIPTS)

FIXTURES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures")


def fixture(name):
    """Absolute path to a tests/fixtures/<name> file."""
    return os.path.join(FIXTURES, name)


def fixture_src(name):
    """Text of a tests/fixtures/<name> file."""
    with open(fixture(name), encoding="utf-8") as f:
        return f.read()
