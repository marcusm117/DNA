"""check_step --status / STATUS.md — the PURE rollup logic (orphan_nodes, changed_files, status_rows,
write_status_md) plus mode_status's dispatch glue. No Lean / no live SMT (matching test_smell.py /
test_find.py: dependencies are monkeypatched, never built for real).
"""
import os

import faithful_lib as L
import check_step as C


class FakeNode:
    """Stand-in for an L.Node — status code only ever reads `.name` off a Main node."""
    def __init__(self, name):
        self.name = name


class FakeOcc:
    """Stand-in for a node OCCURRENCE — subtree_inputs/node_inputs only read `.file` (the container
    file a node is wired in)."""
    def __init__(self, file):
        self.file = file


# ── subtree_inputs scoping (shared-leaf backward-cascade fix) ───────────────────────────────────────
def _patch_cone(monkeypatch, *, cone, backing, occs, main="Book2/Prop11/Main.lean"):
    """Set up a synthetic prop cone. Paths are made absolute under BOOK_ROOT so realpath/relpath round-
    trip back to the given BOOK_ROOT-relative strings."""
    abspath = lambda rel: os.path.join(L.BOOK_ROOT, rel)
    monkeypatch.setattr(L, "cone_names", lambda propdir, root: set(cone))
    monkeypatch.setattr(L, "backing_file", lambda propdir, name: abspath(backing[name]) if backing.get(name) else None)
    monkeypatch.setattr(L, "main_file", lambda propdir: abspath(main))
    monkeypatch.setattr(L, "parse_occurrences",
                        lambda propdir: {n: [FakeOcc(abspath(f)) for f in files] for n, files in occs.items()})


def test_subtree_inputs_excludes_foreign_sibling_container(monkeypatch):
    """step8's cone reuses a shared leaf step8_eb that is ALSO wired in step21.lean (a later Main step's
    backing file). step8's snapshot must contain only the files step8's audit reads — its own backing
    files + Main — NOT step21.lean, so editing step21 never re-stales step8."""
    _patch_cone(
        monkeypatch,
        cone={"step8", "step8_eb"},
        backing={"step8": "Book2/Prop11/step8.lean", "step8_eb": "Book2/Prop11/step8_eb.lean"},
        occs={"step8": ["Book2/Prop11/Main.lean"],
              "step8_eb": ["Book2/Prop11/step8.lean", "Book2/Prop11/step21.lean"]},  # shared in step21
    )
    inputs = L.subtree_inputs("Book2/Prop11", "step8")
    assert inputs == ["Book2/Prop11/Main.lean", "Book2/Prop11/step8.lean", "Book2/Prop11/step8_eb.lean"]
    assert "Book2/Prop11/step21.lean" not in inputs   # the foreign sibling container is dropped


def test_subtree_inputs_keeps_shared_leaf_backing_file(monkeypatch):
    """The shared leaf's OWN backing file stays in the snapshot — a real edit to the leaf must still
    re-stale every cone that reuses it (only the cross-container contamination is dropped)."""
    _patch_cone(
        monkeypatch,
        cone={"step21", "step8_eb"},
        backing={"step21": "Book2/Prop11/step21.lean", "step8_eb": "Book2/Prop11/step8_eb.lean"},
        occs={"step21": ["Book2/Prop11/Main.lean"],
              "step8_eb": ["Book2/Prop11/step8.lean", "Book2/Prop11/step21.lean"]},
    )
    inputs = L.subtree_inputs("Book2/Prop11", "step21")
    # step21's cone reads Main, step21.lean (its own backing/container) and the shared leaf's backing file.
    assert "Book2/Prop11/step8_eb.lean" in inputs       # shared leaf P still tracked
    assert "Book2/Prop11/step21.lean" in inputs          # step21's own container IS in its cone
    assert "Book2/Prop11/step8.lean" not in inputs       # step8's container is foreign to step21's cone


def test_node_inputs_still_keeps_every_container(monkeypatch):
    """The per-node table (used by --whatchanged's blast radius) is UNCHANGED: a shared leaf still lists
    every container it's wired in. Only subtree_inputs (the Main-status snapshot) is scoped."""
    abspath = lambda rel: os.path.join(L.BOOK_ROOT, rel)
    monkeypatch.setattr(L, "backing_file", lambda propdir, name: abspath("Book2/Prop11/step8_eb.lean"))
    occs = {"step8_eb": [FakeOcc(abspath("Book2/Prop11/step8.lean")),
                         FakeOcc(abspath("Book2/Prop11/step21.lean"))]}
    inputs = L.node_inputs("Book2/Prop11", "step8_eb", occs)
    assert "Book2/Prop11/step8.lean" in inputs
    assert "Book2/Prop11/step21.lean" in inputs           # both containers kept (blast radius)


# ── changed_files ─────────────────────────────────────────────────────────────────────────────────
def test_changed_files_classifies_modified_deleted_unchanged(monkeypatch):
    # changed_files hashes via content_sha (the manifest read side — must match the write side, which
    # also stamps content_sha; see content_sha's docstring re @assumption-edit invisibility).
    shas = {"a.lean": "sha_a", "b.lean": "DIFFERENT", "c.lean": None}
    monkeypatch.setattr(L, "content_sha", lambda path: shas[os.path.basename(path)])
    manifest = {"files": {"a.lean": "sha_a", "b.lean": "sha_b", "c.lean": "sha_c"}}
    assert L.changed_files(manifest) == {"b.lean": "modified", "c.lean": "deleted"}


def test_changed_files_empty_manifest_is_empty():
    assert L.changed_files({}) == {}


# ── orphan_nodes ──────────────────────────────────────────────────────────────────────────────────
def test_orphan_nodes_flags_node_reachable_from_no_main_node(monkeypatch):
    occs = {"step1": [], "step2": [], "sub1": [], "old_step3b": []}
    cones = {"step1": {"step1"}, "step2": {"step2", "sub1"}}
    monkeypatch.setattr(L, "parse_occurrences", lambda propdir: occs)
    monkeypatch.setattr(L, "main_nodes_in_order", lambda propdir: [FakeNode("step1"), FakeNode("step2")])
    monkeypatch.setattr(L, "cone_names", lambda propdir, name: cones[name])
    assert L.orphan_nodes("Book2/PropXX") == ["old_step3b"]


def test_orphan_nodes_empty_when_everything_reachable(monkeypatch):
    occs = {"step1": [], "sub1": []}
    monkeypatch.setattr(L, "parse_occurrences", lambda propdir: occs)
    monkeypatch.setattr(L, "main_nodes_in_order", lambda propdir: [FakeNode("step1")])
    monkeypatch.setattr(L, "cone_names", lambda propdir, name: {"step1", "sub1"})
    assert L.orphan_nodes("Book2/PropXX") == []


# ── status_rows ───────────────────────────────────────────────────────────────────────────────────
def _patch_status_deps(monkeypatch, *, main_names, manifest, cones, backing=None,
                        deps_ok=True, integrity_ok=True, orphans=()):
    monkeypatch.setattr(L, "main_nodes_in_order", lambda propdir: [FakeNode(n) for n in main_names])
    monkeypatch.setattr(L, "read_manifest", lambda propdir: manifest)
    monkeypatch.setattr(L, "cone_names", lambda propdir, name: set(cones[name]))
    monkeypatch.setattr(L, "backing_file", lambda propdir, name: (backing or {}).get(name, f"{name}.lean"))
    monkeypatch.setattr(L, "dependency_problems", lambda propdir: [] if deps_ok else ["bad dep"])
    monkeypatch.setattr(L, "integrity_scan", lambda propdir, names=None: [] if integrity_ok else ["bad"])
    monkeypatch.setattr(L, "orphan_nodes", lambda propdir: list(orphans))


def test_status_rows_done_stale_and_todo_with_uncertified_subnode(monkeypatch):
    # Done-ness derives from manifest["subtrees"] (whole-cone certificates), NOT the per-node
    # "certified" table — each rec is {"nodes": [...], "files": {relpath: sha}}. Freshness is the
    # changed_snapshot(rec["files"]) diff. step1 certified+fresh → done; step2 certified but its file
    # changed → stale (which breaks the in-order prefix); step3 has no subtree cert AND is behind the
    # broken prefix → todo, blocked on step2.
    manifest = {
        "subtrees": {
            "step1": {"nodes": ["step1"], "files": {"Book2/PropXX/step1.lean": "h1"}},
            "step2": {"nodes": ["step2"], "files": {"Book2/PropXX/step2.lean": "h2"}},
        },
    }
    monkeypatch.setattr(L, "changed_snapshot",
                        lambda files: {f: "modified" for f in files if "step2" in f})
    _patch_status_deps(monkeypatch, main_names=["step1", "step2", "step3"], manifest=manifest,
                        cones={"step1": {"step1"}, "step2": {"step2"}, "step3": {"step3", "step3_sub"}})
    rows, checks = L.status_rows("Book2/PropXX")
    assert rows[0] == ("step1", "done", "Main subtree certified, inputs fresh")
    assert rows[1][0] == "step2" and rows[1][1] == "stale"
    assert "Book2/PropXX/step2.lean" in rows[1][2]
    assert rows[2][0] == "step3" and rows[2][1] == "todo"
    assert "step2" in rows[2][2]          # blocked behind the stale earlier node
    assert checks == {"deps": True, "integrity": True, "orphans": []}


def test_status_rows_no_backing_file_yet(monkeypatch):
    _patch_status_deps(monkeypatch, main_names=["step4"], manifest={}, cones={"step4": {"step4"}},
                        backing={"step4": None})
    rows, checks = L.status_rows("Book2/PropXX")
    assert rows == [("step4", "todo", "no backing file yet")]


def test_status_rows_surfaces_whole_prop_check_failures(monkeypatch):
    # step1 subtree-certified with an empty file set (changed_snapshot({}) is trivially fresh) → done,
    # so the row is green and the three whole-prop checks are what's under test.
    _patch_status_deps(monkeypatch, main_names=["step1"],
                        manifest={"subtrees": {"step1": {"nodes": ["step1"], "files": {}}}},
                        cones={"step1": {"step1"}}, deps_ok=False, integrity_ok=False,
                        orphans=["old_step3b"])
    rows, checks = L.status_rows("Book2/PropXX")
    assert rows == [("step1", "done", "Main subtree certified, inputs fresh")]
    assert checks == {"deps": False, "integrity": False, "orphans": ["old_step3b"]}


def test_status_rows_tolerant_on_faithful_error(monkeypatch):
    def boom(propdir):
        raise L.FaithfulError("no such node")
    monkeypatch.setattr(L, "main_nodes_in_order", boom)
    rows, checks = L.status_rows("Book2/PropXX")
    assert rows == []
    assert "error" in checks and "no such node" in checks["error"]


# ── write_status_md ───────────────────────────────────────────────────────────────────────────────
def test_write_status_md_renders_deterministic_table(tmp_path, monkeypatch):
    rows = [("step1", "done", "cone certified, inputs fresh"),
            ("step2", "stale", "step2.lean changed since audit (--subtree step2)")]
    checks = {"deps": True, "integrity": True, "orphans": []}
    monkeypatch.setattr(L, "status_rows", lambda propdir: (rows, checks))
    propdir = str(tmp_path)
    L.write_status_md(propdir, "--subtree step2")
    content = open(os.path.join(propdir, "STATUS.md"), encoding="utf-8").read()
    assert "do not hand-edit" in content
    assert "Snapshot as of audit: `--subtree step2`" in content
    assert "| 1  | step1 | ✓ | cone certified, inputs fresh |" in content
    assert "| 2  | step2 | ⚠ |" in content
    assert "1/2 Main nodes" in content
    assert "NOT all-green" in content
    # deterministic: re-render is byte-identical
    L.write_status_md(propdir, "--subtree step2")
    assert open(os.path.join(propdir, "STATUS.md"), encoding="utf-8").read() == content


def test_write_status_md_all_green_verdict(tmp_path, monkeypatch):
    rows = [("step1", "done", "cone certified, inputs fresh")]
    checks = {"deps": True, "integrity": True, "orphans": []}
    monkeypatch.setattr(L, "status_rows", lambda propdir: (rows, checks))
    propdir = str(tmp_path)
    L.write_status_md(propdir, "--all")
    content = open(os.path.join(propdir, "STATUS.md"), encoding="utf-8").read()
    assert "GUARANTEED to pass" in content


def test_write_status_md_error_path(tmp_path, monkeypatch):
    monkeypatch.setattr(L, "status_rows", lambda propdir: ([], {"error": "boom"}))
    propdir = str(tmp_path)
    L.write_status_md(propdir, "--all")
    content = open(os.path.join(propdir, "STATUS.md"), encoding="utf-8").read()
    assert "ERROR rendering status: boom" in content


# ── mode_status (via the real dispatch) ──────────────────────────────────────────────────────────
def _propdir(tmp_path):
    open(os.path.join(tmp_path, "Main.lean"), "w", encoding="utf-8").close()
    return str(tmp_path)


def test_main_status_empty_manifest_guidance(tmp_path, monkeypatch, capsys):
    propdir = _propdir(tmp_path)
    monkeypatch.setattr(C.L, "read_manifest", lambda p: {})
    monkeypatch.setattr(C.L, "main_nodes_in_order", lambda p: [FakeNode("step1"), FakeNode("step2")])
    code = C.main([propdir, "--status"])
    out = capsys.readouterr().out
    assert code == 0
    assert "no certification manifest yet" in out
    assert "--drive" in out            # --drive is the default driving command (not hand-run --subtree)
    assert "then step2" in out


def test_main_status_empty_manifest_no_nodes_yet(tmp_path, monkeypatch, capsys):
    propdir = _propdir(tmp_path)
    monkeypatch.setattr(C.L, "read_manifest", lambda p: {})
    monkeypatch.setattr(C.L, "main_nodes_in_order", lambda p: [])
    code = C.main([propdir, "--status"])
    out = capsys.readouterr().out
    assert code == 0
    assert "map the sentences first" in out


def test_main_status_board_not_all_green(tmp_path, monkeypatch, capsys):
    propdir = _propdir(tmp_path)
    monkeypatch.setattr(C.L, "read_manifest", lambda p: {"certified": {"step1": {}}})
    rows = [("step1", "done", "cone certified, inputs fresh"),
            ("step2", "todo", "no backing file yet")]
    checks = {"deps": True, "integrity": True, "orphans": []}
    monkeypatch.setattr(C.L, "status_rows", lambda p: (rows, checks))
    code = C.main([propdir, "--status"])
    out = capsys.readouterr().out
    assert code == 0
    assert "✓ step1" in out and "○ step2" in out
    assert "SUMMARY: 1/2 Main nodes" in out
    assert "NOT all-green" in out
    assert "--subtree step2" in out


def test_main_status_board_all_green(tmp_path, monkeypatch, capsys):
    propdir = _propdir(tmp_path)
    monkeypatch.setattr(C.L, "read_manifest", lambda p: {"certified": {"step1": {}}})
    rows = [("step1", "done", "cone certified, inputs fresh")]
    checks = {"deps": True, "integrity": True, "orphans": []}
    monkeypatch.setattr(C.L, "status_rows", lambda p: (rows, checks))
    code = C.main([propdir, "--status"])
    out = capsys.readouterr().out
    assert code == 0
    assert "GUARANTEED to pass" in out


def test_main_status_board_reports_orphans(tmp_path, monkeypatch, capsys):
    propdir = _propdir(tmp_path)
    monkeypatch.setattr(C.L, "read_manifest", lambda p: {"certified": {"step1": {}}})
    rows = [("step1", "done", "cone certified, inputs fresh")]
    checks = {"deps": True, "integrity": True, "orphans": ["old_step3b"]}
    monkeypatch.setattr(C.L, "status_rows", lambda p: (rows, checks))
    code = C.main([propdir, "--status"])
    out = capsys.readouterr().out
    assert code == 0
    assert "no orphans" in out and "old_step3b" in out
    assert "orphan old_step3b (wire it or delete it)" in out


def test_main_status_checklist_alias(tmp_path, monkeypatch, capsys):
    propdir = _propdir(tmp_path)
    monkeypatch.setattr(C.L, "read_manifest", lambda p: {})
    monkeypatch.setattr(C.L, "main_nodes_in_order", lambda p: [FakeNode("step1")])
    code = C.main([propdir, "--checklist"])
    out = capsys.readouterr().out
    assert code == 0
    assert "no certification manifest yet" in out


# ── write_status_md wired into _restamp_node (the per-node PASS path) ───────────────────────────────
def test_restamp_node_calls_write_status_md(monkeypatch):
    calls = []
    monkeypatch.setattr(L, "parse_occurrences", lambda propdir: {})
    monkeypatch.setattr(L, "read_manifest", lambda propdir: {})
    monkeypatch.setattr(L, "node_inputs", lambda propdir, name, occs: [])
    monkeypatch.setattr(L, "write_manifest", lambda propdir, manifest: None)
    monkeypatch.setattr(L, "write_status_md", lambda propdir, source: calls.append((propdir, source)))
    C._restamp_node("Book2/PropXX", "step1", "leaf")
    assert calls == [("Book2/PropXX", "node step1")]


def test_restamp_node_tolerates_write_status_md_raising(monkeypatch):
    monkeypatch.setattr(L, "parse_occurrences", lambda propdir: {})
    monkeypatch.setattr(L, "read_manifest", lambda propdir: {})
    monkeypatch.setattr(L, "node_inputs", lambda propdir, name, occs: [])
    monkeypatch.setattr(L, "write_manifest", lambda propdir, manifest: None)
    monkeypatch.setattr(L, "write_status_md", lambda propdir, source: (_ for _ in ()).throw(RuntimeError("boom")))
    C._restamp_node("Book2/PropXX", "step1", "leaf")   # must not raise — bookkeeping is best-effort


# ── write_status_md wired into _audit_with_manifest (the --all/--subtree path) ──────────────────────
def test_audit_with_manifest_calls_write_status_md_on_pass(monkeypatch):
    calls = []
    monkeypatch.setattr(L, "parse_occurrences", lambda propdir: {})
    monkeypatch.setattr(L, "read_manifest", lambda propdir: {})
    monkeypatch.setattr(L, "node_inputs", lambda propdir, name, occs: [])
    monkeypatch.setattr(L, "write_manifest", lambda propdir, manifest: None)
    monkeypatch.setattr(L, "write_status_md", lambda propdir, source: calls.append((propdir, source)))
    monkeypatch.setattr(C, "_audit", lambda propdir, order, success_msg, on_pass=None: 0)
    code = C._audit_with_manifest("Book2/PropXX", [], "ok", source="--all")
    assert code == 0
    assert calls == [("Book2/PropXX", "--all")]


def test_audit_with_manifest_calls_write_status_md_even_on_failure(monkeypatch):
    """The manifest + STATUS.md must persist the certified bottom-up PREFIX even when the audit
    stops at a failure partway through — that's the whole point of recording in `finally`."""
    calls = []
    monkeypatch.setattr(L, "parse_occurrences", lambda propdir: {})
    monkeypatch.setattr(L, "read_manifest", lambda propdir: {})
    monkeypatch.setattr(L, "node_inputs", lambda propdir, name, occs: [])
    monkeypatch.setattr(L, "write_manifest", lambda propdir, manifest: None)
    monkeypatch.setattr(L, "write_status_md", lambda propdir, source: calls.append((propdir, source)))
    monkeypatch.setattr(C, "_audit", lambda propdir, order, success_msg, on_pass=None: 1)
    code = C._audit_with_manifest("Book2/PropXX", [], "ok", source="--subtree step5")
    assert code == 1
    assert calls == [("Book2/PropXX", "--subtree step5")]


def test_audit_with_manifest_tolerates_write_status_md_raising(monkeypatch):
    monkeypatch.setattr(L, "parse_occurrences", lambda propdir: {})
    monkeypatch.setattr(L, "read_manifest", lambda propdir: {})
    monkeypatch.setattr(L, "node_inputs", lambda propdir, name, occs: [])
    monkeypatch.setattr(L, "write_manifest", lambda propdir, manifest: None)
    monkeypatch.setattr(L, "write_status_md", lambda propdir, source: (_ for _ in ()).throw(RuntimeError("boom")))
    monkeypatch.setattr(C, "_audit", lambda propdir, order, success_msg, on_pass=None: 0)
    code = C._audit_with_manifest("Book2/PropXX", [], "ok", source="--all")
    assert code == 0          # the audit's own exit code must survive a STATUS.md rendering crash


# ── orphan guard inserted into mode_all ──────────────────────────────────────────────────────────────
def test_mode_all_aborts_on_orphan_before_any_build_work(monkeypatch):
    """Orphans must short-circuit BEFORE the dependency check / audit_order / _audit_with_manifest —
    monkeypatch those to explode if reached, so the test fails loudly if the guard's placement regresses."""
    monkeypatch.setattr(L, "integrity_scan", lambda propdir: [])
    monkeypatch.setattr(L, "orphan_nodes", lambda propdir: ["old_step3b"])

    def boom(*a, **k):
        raise AssertionError("should not be reached — orphan guard must short-circuit first")
    monkeypatch.setattr(C, "_run_dependency", boom)
    monkeypatch.setattr(L, "audit_order", boom)
    monkeypatch.setattr(C, "_audit_with_manifest", boom)

    code = C.mode_all("Book2/PropXX")
    assert code == 1


def test_mode_all_orphan_message_names_the_node(monkeypatch, capsys):
    monkeypatch.setattr(L, "integrity_scan", lambda propdir: [])
    monkeypatch.setattr(L, "orphan_nodes", lambda propdir: ["old_step3b"])
    monkeypatch.setattr(C, "_run_dependency", lambda propdir: (_ for _ in ()).throw(
        AssertionError("should not be reached")))
    code = C.mode_all("Book2/PropXX")
    out = capsys.readouterr().out
    assert code == 1
    assert "old_step3b" in out
    assert "orphan" in out.lower()


def test_mode_all_proceeds_past_empty_orphans_to_dependency_check(monkeypatch):
    """With no orphans, mode_all must still reach the (pre-existing) dependency check — proves the new
    guard doesn't accidentally swallow every call, only the orphan-positive case."""
    monkeypatch.setattr(L, "integrity_scan", lambda propdir: [])
    monkeypatch.setattr(L, "orphan_nodes", lambda propdir: [])
    monkeypatch.setattr(C, "_run_dependency", lambda propdir: False)   # simulate a dependency failure
    code = C.mode_all("Book2/PropXX")
    assert code == 1   # reached and failed the (mocked) dependency check, not the orphan guard
