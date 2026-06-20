"""ensure_fresh — incremental re-parse: only changed files re-parse; removed files drop their rows.

Drives bake_index.ensure_fresh against a TEMP target set (monkeypatched paths + scan_targets) so the
real `.lake/index.jsonl` is never touched."""
import json
import os
import shutil

import bake_index as B
from conftest import fixture


def _setup_tmp(tmp_path, files):
    """Copy named fixtures into tmp_path, point bake_index's index/manifest/lock + scan_targets there."""
    targets = []
    for fx in files:
        dst = os.path.join(tmp_path, fx)
        shutil.copy(fixture(fx), dst)
        targets.append(dst)
    B.INDEX_PATH = os.path.join(tmp_path, "index.jsonl")
    B.MANIFEST_PATH = os.path.join(tmp_path, "index.manifest.json")
    B.LOCK_PATH = os.path.join(tmp_path, "index.lock")
    B.scan_targets = lambda: sorted(targets)
    return targets


def _restore():
    import importlib
    importlib.reload(B)


def test_incremental_reparse_and_removal(tmp_path):
    tmp = str(tmp_path)
    targets = _setup_tmp(tmp, ["axiom_neg.lean", "prop_family.lean"])
    try:
        rows, changed = B.ensure_fresh(force=True)
        assert changed == 2
        names0 = {r["name"] for r in rows}
        assert "between_symm" in names0 and "proposition_5" in names0

        # 2nd call, nothing changed → 0 re-parsed
        _, changed2 = B.ensure_fresh()
        assert changed2 == 0

        # edit one file (append a new axiom) → only that file re-parses, new row appears
        with open(targets[0], "a", encoding="utf-8") as f:
            f.write("\naxiom extra_ax : ∀ (a b : Point), a ≠ b → a.onLine AB\n")
        # bump mtime deterministically forward
        st = os.stat(targets[0])
        os.utime(targets[0], (st.st_atime, st.st_mtime + 5))
        rows3, changed3 = B.ensure_fresh()
        assert changed3 == 1
        assert "extra_ax" in {r["name"] for r in rows3}
        assert "proposition_5" in {r["name"] for r in rows3}   # untouched file's rows survive

        # remove a target → its rows drop
        targets.pop(1)                                  # drop prop_family.lean from the target set
        B.scan_targets = lambda: sorted(targets)
        rows4, _ = B.ensure_fresh()
        assert "proposition_5" not in {r["name"] for r in rows4}
        assert "between_symm" in {r["name"] for r in rows4}
    finally:
        _restore()


def test_add_brand_new_file_reparses_only_it(tmp_path):
    """The 'if I ADD a file, does it rebuild?' case — distinct from editing an existing one (it hits the
    `prev is None` branch). Add a new path to the target set and confirm only it re-parses."""
    tmp = str(tmp_path)
    targets = _setup_tmp(tmp, ["axiom_neg.lean"])
    try:
        rows, changed = B.ensure_fresh(force=True)
        assert changed == 1
        assert "between_symm" in {r["name"] for r in rows}
        assert "proposition_5" not in {r["name"] for r in rows}

        # ADD a brand-new file to the search space
        new = os.path.join(tmp, "prop_family.lean")
        shutil.copy(fixture("prop_family.lean"), new)
        targets.append(new)
        B.scan_targets = lambda: sorted(targets)

        rows2, changed2 = B.ensure_fresh()
        assert changed2 == 1                                    # ONLY the new file parsed
        names = {r["name"] for r in rows2}
        assert "proposition_5" in names                         # new file's rows now present
        assert "between_symm" in names                          # the untouched file's rows survive
    finally:
        _restore()


def test_mtime_touch_without_content_change_no_reparse(tmp_path):
    """mtime fast-path + sha secondary check: touching a file (new mtime, identical bytes) must NOT
    trigger a re-parse — the sha matches, so the manifest just refreshes its mtime."""
    tmp = str(tmp_path)
    targets = _setup_tmp(tmp, ["axiom_neg.lean"])
    try:
        B.ensure_fresh(force=True)
        st = os.stat(targets[0])
        os.utime(targets[0], (st.st_atime, st.st_mtime + 10))   # new mtime, SAME content
        _, changed = B.ensure_fresh()
        assert changed == 0                                     # sha unchanged → no re-parse
    finally:
        _restore()


def test_find_main_auto_rebakes_on_query(tmp_path, capsys):
    """find.py's promise is that EVERY query re-bakes. With a temp target set, editing a file then
    running find.main() must reflect the new declaration in stdout (no stale index)."""
    import find as F
    tmp = str(tmp_path)
    targets = _setup_tmp(tmp, ["axiom_neg.lean"])
    try:
        B.ensure_fresh(force=True)                              # seed the index
        # add a new axiom to the file
        with open(targets[0], "a", encoding="utf-8") as f:
            f.write("\naxiom freshly_added_ax : ∀ (a b : Point), a ≠ b → a.onLine AB\n")
        st = os.stat(targets[0])
        os.utime(targets[0], (st.st_atime, st.st_mtime + 5))
        code = F.main(["--name", "freshly_added_ax"])           # a query → should auto-rebake first
        out = capsys.readouterr().out
        assert code == 0
        assert "freshly_added_ax" in out                        # the just-added decl is found
    finally:
        _restore()


def test_schema_bump_forces_full_rebuild(tmp_path):
    tmp = str(tmp_path)
    _setup_tmp(tmp, ["axiom_neg.lean"])
    try:
        B.ensure_fresh(force=True)
        # write a manifest with a stale schema → next ensure_fresh must rebuild (changed > 0)
        with open(B.MANIFEST_PATH, "w", encoding="utf-8") as f:
            json.dump({"_schema": -1, "files": {}}, f)
        _, changed = B.ensure_fresh()
        assert changed >= 1
    finally:
        _restore()
