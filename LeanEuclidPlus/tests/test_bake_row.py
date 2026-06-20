"""bake_index.parse_file — full row schema over the fixture .lean snippets."""
import bake_index as B
from conftest import fixture


def _by_name(rows):
    return {r["name"]: r for r in rows}


def test_axiom_row_schema_and_negation():
    rows = _by_name(B.parse_file(fixture("axiom_neg.lean")))
    r = rows["between_symm"]
    assert r["kind"] == "axiom"
    assert r["object_arity"] == 3
    assert r["concludes_exists"] is False
    assert r["cited_props"] == []
    # docstring captured; trailing -- comment does NOT leak into the signature
    assert "symmetry" in r["docstring"]
    assert "--" not in r["signature"]
    syms = {(f["symbol"], f["role"], f["polarity"]) for f in r["facts"]}
    assert ("between", "hyp", "pos") in syms
    assert ("between", "concl", "neg") in syms          # ¬(between b a c)
    assert ("ne", "concl", "neg") in syms               # (a ≠ b)


def test_construction_exists_flag_and_concl_facts():
    rows = _by_name(B.parse_file(fixture("construction_exists.lean")))
    r = rows["line_from_points"]
    assert r["concludes_exists"] is True
    # the ∃-body conclusion facts are still extracted
    assert any(f["symbol"] == "onLine" and f["role"] == "concl" for f in r["facts"])
    # the `a ≠ b` hypothesis is recorded
    assert any(f["symbol"] == "ne" and f["role"] == "hyp" for f in r["facts"])


def test_helper_curried_classification_and_citations():
    rows = _by_name(B.parse_file(fixture("helper_curried.lean")))
    r = rows["sample_helper"]
    # classified `theorem`: it is neither `helper_`-named nor under Helpers/ (the two helper triggers).
    # (Real Helpers/*.lean lemmas classify as `helper` via the path; this fixture exercises only the
    # curried-binder parsing + citation extraction, which are kind-independent.)
    assert r["kind"] == "theorem"
    assert r["object_arity"] == 5                       # p q w (Point) + L M (Line)
    # citations from the body (prop + construction)
    assert "proposition_30" in r["cited_props"]
    assert "line_from_points" in r["cited_props"]
    # the curried hyp binders are treated as hypotheses (atomic-fact + parallelogram)
    assert any(f["symbol"] == "intersectsLine" and f["role"] == "hyp" for f in r["facts"])
    assert any(f["symbol"] == "formParallelogram" and f["role"] == "hyp" for f in r["facts"])
    # conclusion fact
    assert any(f["symbol"] == "sameSide" and f["role"] == "concl" for f in r["facts"])


def test_prop_family_distinct_rows_with_primes():
    rows = _by_name(B.parse_file(fixture("prop_family.lean")))
    assert "proposition_5" in rows
    assert "proposition_5'" in rows
    assert rows["proposition_5"]["kind"] == "prop"
    assert rows["proposition_5'"]["kind"] == "prop"
    # the primed variant cites the base one
    assert "proposition_5" in rows["proposition_5'"]["cited_props"]
    # raw_name carries the namespace
    assert rows["proposition_5"]["raw_name"] == "Elements.Book1.proposition_5"


def test_path_classification_against_real_tree():
    """The `helper` vs `step` distinction is PATH-based (Helpers/ vs Book*/Prop*/stepN.lean), which the
    fixtures can't exercise — check it against the real source tree instead."""
    import os
    import faithful_lib as L
    helpers_dir = os.path.join(L.BOOK_ROOT, "Helpers")
    if os.path.isdir(helpers_dir):
        hits = [f for f in os.listdir(helpers_dir) if f.endswith(".lean")]
        if hits:
            rows = B.parse_file(os.path.join(helpers_dir, hits[0]))
            kinds = {r["kind"] for r in rows if r["name"].startswith(("offLine", "sameSide", "not_",
                                                                       "parallelogram", "right_"))}
            assert kinds <= {"helper"} or "helper" in {r["kind"] for r in rows}
    step1 = os.path.join(L.BOOK_ROOT, "Book2", "Prop01", "step1.lean")
    if os.path.exists(step1):
        rows = _by_name(B.parse_file(step1))
        assert rows["helper_2_1_step1"]["kind"] == "step"


def test_no_error_rows_in_fixtures():
    for fx in ("axiom_neg.lean", "construction_exists.lean", "helper_curried.lean",
               "prop_family.lean", "relations_min.lean"):
        rows = B.parse_file(fixture(fx))
        assert not any(r["kind"] == "_error" for r in rows), f"parse error in {fx}: {rows}"
