"""Tests for the step_order_hook PreToolUse hook (in-order step discipline enforcement).

Tests the core logic functions in isolation (main_node_names, find_frontier, main_level_ancestor)
and the end-to-end decision via subprocess (simulating the hook's stdin/stdout protocol).
"""
import json, os, shutil, subprocess, sys, tempfile

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", ".claude", "hooks"))
# Can't import step_order_hook directly (it calls sys.exit on import-time allow/deny),
# but we can import its pure functions by mocking sys.exit or just test via subprocess.
# Instead, we'll inline-test the logic functions by importing the module carefully.

HOOK_PATH = os.path.realpath(os.path.join(
    os.path.dirname(__file__), "..", "..", ".claude", "hooks", "step_order_hook.py"))
LEAN_ROOT = os.path.realpath(os.path.join(os.path.dirname(__file__), ".."))


def run_hook(file_path):
    """Run the hook as a subprocess with a simulated PreToolUse JSON on stdin.
    Returns (decision, reason) or (None, None) for allow (no output)."""
    inp = json.dumps({"tool_input": {"file_path": file_path}})
    result = subprocess.run(
        [sys.executable, HOOK_PATH],
        input=inp, capture_output=True, text=True, timeout=10)
    assert result.returncode == 0, f"Hook crashed: {result.stderr}"
    if not result.stdout.strip():
        return None, None  # allow
    data = json.loads(result.stdout)
    out = data["hookSpecificOutput"]
    return out["permissionDecision"], out["permissionDecisionReason"]


# ── main_node_names tests (via a temp Main.lean) ─────────────────────────────

def _write_main(tmp, content):
    main = os.path.join(tmp, "Main.lean")
    with open(main, "w") as f:
        f.write(content)
    return main


def test_main_node_names_parses_sentences():
    # Import the function directly (no sys.exit on import at module level)
    import importlib.util
    spec = importlib.util.spec_from_file_location("hook", HOOK_PATH)
    mod = importlib.util.module_from_spec(spec)
    # Patch sys.exit so allow()/deny() don't kill us
    original_exit = sys.exit
    sys.exit = lambda code=0: None
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.exit = original_exit

    with tempfile.TemporaryDirectory() as tmp:
        main = _write_main(tmp, '''
  euclid_sentence "2.14.1" "blah" (step1 : foo) := by sorry
  euclid_sentence "2.14.2" "blah" (step2 : bar) := by sorry
  have fp : formParallelogram := by sorry
  have hcase : True := by
    trivial
''')
        names = mod.main_node_names(main)
        # Should find step1, step2, fp (sorry nodes) but NOT hcase (real body)
        assert "step1" in names
        assert "step2" in names
        assert "fp" in names
        assert "hcase" not in names


def test_main_node_names_ignores_indented_haves():
    import importlib.util
    spec = importlib.util.spec_from_file_location("hook", HOOK_PATH)
    mod = importlib.util.module_from_spec(spec)
    original_exit = sys.exit
    sys.exit = lambda code=0: None
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.exit = original_exit

    with tempfile.TemporaryDirectory() as tmp:
        main = _write_main(tmp, '  euclid_sentence "2.14.1" "blah" (step1 : foo) := by sorry\n'
                                '        have step2_inner : bar := by sorry\n'
                                '        have step3_deep : baz := by sorry\n')
        names = mod.main_node_names(main)
        assert "step1" in names
        # Deeply indented haves (col > 4) should NOT be Main-level
        assert "step2_inner" not in names
        assert "step3_deep" not in names


# ── main_level_ancestor tests ─────────────────────────────────────────────────

def test_main_level_ancestor():
    import importlib.util
    spec = importlib.util.spec_from_file_location("hook", HOOK_PATH)
    mod = importlib.util.module_from_spec(spec)
    original_exit = sys.exit
    sys.exit = lambda code=0: None
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.exit = original_exit

    nodes = ["fp", "step1", "step2", "step10", "step11", "between_ahb"]

    # Exact matches
    assert mod.main_level_ancestor("step1.lean", nodes) == "step1"
    assert mod.main_level_ancestor("step10.lean", nodes) == "step10"
    assert mod.main_level_ancestor("between_ahb.lean", nodes) == "between_ahb"
    assert mod.main_level_ancestor("fp.lean", nodes) == "fp"

    # Sub-node matches (prefix + underscore)
    assert mod.main_level_ancestor("step1_foo.lean", nodes) == "step1"
    assert mod.main_level_ancestor("step10_bar.lean", nodes) == "step10"
    assert mod.main_level_ancestor("step11_baz_qux.lean", nodes) == "step11"

    # step1_foo should NOT match step10 (longest-prefix-first ensures step10 > step1)
    assert mod.main_level_ancestor("step10_x.lean", nodes) == "step10"

    # No match
    assert mod.main_level_ancestor("scratch.lean", nodes) is None
    assert mod.main_level_ancestor("helper.lean", nodes) is None


# ── end-to-end hook tests (against real Prop14 on disk) ───────────────────────
# These exercise the REAL status_rows + manifest path on a real prop (the synthetic-prop tests below
# stub the manifest). They must NOT hardcode "step8 is Prop14's frontier": the live frontier drifts as
# proof work certifies more steps, AND a tooling change to the cert hash (e.g. the content_sha comment-
# strip broadening) re-stales a prop's certified prefix as a one-time migration, regressing the frontier.
# So we derive the frontier from the same board the hook uses and assert the migration-stable invariants:
# the frontier file (and its sub-nodes) is always editable, and a certified before-frontier node is too.

def _load_hook():
    """Import the hook module without letting its import-time allow()/deny() sys.exit kill us."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("hook", HOOK_PATH)
    mod = importlib.util.module_from_spec(spec)
    original_exit = sys.exit
    sys.exit = lambda code=0: None
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.exit = original_exit
    return mod


PROP14 = os.path.join(LEAN_ROOT, "Book2", "Prop14")


def test_hook_allows_frontier_step():
    """Writing the current frontier step is always allowed (whatever the live frontier is)."""
    frontier, _names, _state = _load_hook().find_frontier(PROP14)
    if frontier is None:
        pytest.skip("Prop14 fully certified — no frontier to test")
    decision, _ = run_hook(os.path.join(PROP14, f"{frontier}.lean"))
    assert decision is None  # allow


def test_hook_allows_frontier_subnode():
    """Sub-nodes of the frontier step should be allowed."""
    frontier, _names, _state = _load_hook().find_frontier(PROP14)
    if frontier is None:
        pytest.skip("Prop14 fully certified — no frontier to test")
    decision, _ = run_hook(os.path.join(PROP14, f"{frontier}_subnode_smoke.lean"))
    assert decision is None


def test_hook_allows_certified_step():
    """A node BEFORE the frontier is certified/done — editing it should be allowed."""
    frontier, names, _state = _load_hook().find_frontier(PROP14)
    if frontier is None or names.index(frontier) == 0:
        pytest.skip("no certified before-frontier node on Prop14 right now")
    before = names[names.index(frontier) - 1]
    decision, _ = run_hook(os.path.join(PROP14, f"{before}.lean"))
    assert decision is None


def test_hook_allows_main_lean():
    """Main.lean is always allowed regardless of frontier."""
    path = os.path.join(LEAN_ROOT, "Book2", "Prop14", "Main.lean")
    decision, _ = run_hook(path)
    assert decision is None


def test_hook_allows_non_lean_file():
    """Non-.lean files are never gated."""
    path = os.path.join(LEAN_ROOT, "Book2", "Prop14", "agent_notes.md")
    decision, _ = run_hook(path)
    assert decision is None


def test_hook_allows_helpers_dir():
    """Files outside Book*/Prop*/ are never gated."""
    path = os.path.join(LEAN_ROOT, "Helpers", "OffLine.lean")
    decision, _ = run_hook(path)
    assert decision is None


def test_hook_allows_no_manifest_prop():
    """Props with no manifest (e.g. Prop04 with wiped .lake/) allow everything."""
    path = os.path.join(LEAN_ROOT, "Book2", "Prop04", "step5.lean")
    decision, _ = run_hook(path)
    assert decision is None


def test_hook_allows_fp_node():
    """fp is a certified Main node in Prop14 — should be allowed."""
    path = os.path.join(LEAN_ROOT, "Book2", "Prop14", "fp.lean")
    decision, _ = run_hook(path)
    assert decision is None


PROP11 = os.path.join(LEAN_ROOT, "Book2", "Prop11")


def test_hook_allows_subnode_of_non_beyond_frontier_node_in_prop11():
    """A sub-node of a node AT-OR-BEFORE the frontier is allowed (e.g. `step8_ahb_mag.lean` when step8
    is certified). Derived from the LIVE board — NOT hardcoded "step8 is certified in Prop11" — so it
    can't rot as Prop11's frontier drifts (a cert-hash migration can re-stale the certified prefix and
    pull the frontier back to step1, which is exactly what broke the old hardcoded assertion)."""
    frontier, names, _state = _load_hook().find_frontier(PROP11)
    if frontier is None:
        pytest.skip("Prop11 fully certified — no frontier to test")
    # Prefer a node strictly BEFORE the frontier (a certified node); fall back to the frontier itself
    # (whose sub-nodes are also allowed). Both give ancestor_idx <= frontier_idx → allow.
    idx = names.index(frontier)
    target = names[idx - 1] if idx > 0 else names[idx]
    decision, _ = run_hook(os.path.join(PROP11, f"{target}_ahb_mag.lean"))
    assert decision is None


# ── end-to-end DENY tests (synthetic prop, NOT live repo state) ───────────────
# The deny path is gated on the frontier (first uncertified Main node). Asserting it against a real
# prop (Prop14/Prop11) is fragile: as proof work certifies more steps the frontier advances and the
# once-denied step becomes allowed, silently rotting the test. So we stand up a throwaway prop under
# the real LeanEuclidPlus tree (the hook resolves its manifest path relative to that root, so the
# fixture must live there) with a hand-written manifest pinning the frontier at step2, and tear it
# down after. Frontier is fully under our control → the deny assertions never drift.

def _build_synthetic_prop(subtrees):
    """Write Book9/Prop1/Main.lean (steps 1–3, all `:= by sorry`) + a manifest with the given
    `subtrees` dict. Returns (propdir, manifest_path). Caller is responsible for teardown."""
    propdir = os.path.join(LEAN_ROOT, "Book9", "Prop1")
    cert_dir = os.path.join(LEAN_ROOT, ".lake", "faithful-certified")
    manifest_path = os.path.join(cert_dir, "Book9_Prop1.json")
    os.makedirs(propdir, exist_ok=True)
    os.makedirs(cert_dir, exist_ok=True)
    with open(os.path.join(propdir, "Main.lean"), "w", encoding="utf-8") as f:
        f.write(
            '  euclid_sentence "9.1.1" "blah" (step1 : foo) := by sorry\n'
            '  euclid_sentence "9.1.2" "blah" (step2 : bar) := by sorry\n'
            '  euclid_sentence "9.1.3" "blah" (step3 : baz) := by sorry\n')
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump({"subtrees": subtrees}, f)
    return propdir, manifest_path


def _teardown_synthetic_prop(manifest_path):
    shutil.rmtree(os.path.join(LEAN_ROOT, "Book9"), ignore_errors=True)
    if os.path.exists(manifest_path):
        os.remove(manifest_path)


@pytest.fixture
def synthetic_prop():
    """Manifest certifies ONLY step1 (fresh), so the frontier is the uncertified step2."""
    propdir, mp = _build_synthetic_prop({"step1": {"nodes": ["step1"], "files": {}}})
    try:
        yield propdir
    finally:
        _teardown_synthetic_prop(mp)


@pytest.fixture
def stale_prop():
    """step1 certified+fresh AND step2 certified-but-STALE — step2's recorded input hash for the
    (existing) Main.lean is bogus, so changed_snapshot flags it modified ⟹ step2 is the frontier.
    This is the regression the staleness-aware hook fixes: presence-only would treat step2 as done
    (it IS a subtrees key) and let work proceed to step3. Reaching this verdict REQUIRES the hook's
    status_rows path to run (presence-only can't see staleness), so this also exercises that path."""
    propdir, mp = _build_synthetic_prop({
        "step1": {"nodes": ["step1"], "files": {}},
        "step2": {"nodes": ["step2"],
                  "files": {"Book9/Prop1/Main.lean": "bogus-sha-does-not-match-disk"}},
    })
    try:
        yield propdir
    finally:
        _teardown_synthetic_prop(mp)


def test_hook_denies_past_frontier(synthetic_prop):
    """step3 is two past the frontier (step2) — should be denied, naming the frontier + 'IN ORDER'."""
    decision, reason = run_hook(os.path.join(synthetic_prop, "step3.lean"))
    assert decision == "deny"
    assert "step2" in reason       # names the frontier to certify first
    assert "IN ORDER" in reason


def test_hook_denies_subnode_past_frontier(synthetic_prop):
    """A sub-node of a past-frontier step (step3_foo) is denied too — gated on its Main ancestor."""
    decision, reason = run_hook(os.path.join(synthetic_prop, "step3_foo.lean"))
    assert decision == "deny"
    assert "step3" in reason       # the ancestor it belongs to


def test_hook_allows_frontier_in_synthetic_prop(synthetic_prop):
    """The frontier step itself (step2) and its sub-nodes are allowed; the certified step1 too."""
    assert run_hook(os.path.join(synthetic_prop, "step2.lean"))[0] is None
    assert run_hook(os.path.join(synthetic_prop, "step2_foo.lean"))[0] is None
    assert run_hook(os.path.join(synthetic_prop, "step1.lean"))[0] is None


# ── staleness-aware frontier: a certified-but-stale node HARD-STOPS later work ────────────────────────

def test_hook_denies_past_stale_frontier(stale_prop):
    """step3 is past a STALE step2 — denied, even though step2 is a subtrees key (presence-only would
    have wrongly allowed step3). The reason must name step2 and flag it STALE."""
    decision, reason = run_hook(os.path.join(stale_prop, "step3.lean"))
    assert decision == "deny"
    assert "step2" in reason
    assert "STALE" in reason
    assert "IN ORDER" in reason


def test_hook_allows_editing_the_stale_node(stale_prop):
    """The stale frontier (step2) and its sub-nodes must be ALLOWED so the agent can re-certify it;
    the earlier fresh step1 too."""
    assert run_hook(os.path.join(stale_prop, "step2.lean"))[0] is None
    assert run_hook(os.path.join(stale_prop, "step2_foo.lean"))[0] is None
    assert run_hook(os.path.join(stale_prop, "step1.lean"))[0] is None


def test_hook_handles_invalid_json_gracefully():
    """Unparseable stdin should allow (never block the pipeline)."""
    result = subprocess.run(
        [sys.executable, HOOK_PATH],
        input="not json at all", capture_output=True, text=True, timeout=10)
    assert result.returncode == 0
    assert result.stdout.strip() == ""  # allow


def test_hook_handles_empty_file_path():
    """Empty file_path should allow."""
    inp = json.dumps({"tool_input": {"file_path": ""}})
    result = subprocess.run(
        [sys.executable, HOOK_PATH],
        input=inp, capture_output=True, text=True, timeout=10)
    assert result.returncode == 0
    assert result.stdout.strip() == ""
