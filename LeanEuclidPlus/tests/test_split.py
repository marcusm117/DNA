"""split_signature / split_quantifier_and_arrow / split_conjuncts — the type-region scanners."""
import faithful_lib as L


def test_forall_peel_and_arrow():
    t = "∀ (a b c : Point), between a b c → (between c b a) ∧ (a ≠ b)"
    binders, hyps, concl, exists_ = L.split_quantifier_and_arrow(t)
    assert binders == "(a b c : Point)"
    assert hyps.strip() == "between a b c"
    assert concl == "(between c b a) ∧ (a ≠ b)"
    assert exists_ is False


def test_multiple_hyps_join_on_arrow():
    # only the LAST arrow segment is the conclusion; everything before is hypotheses
    t = "∀ (a : Point), P a → Q a → R a"
    _, hyps, concl, _ = L.split_quantifier_and_arrow(t)
    assert "P a" in hyps and "Q a" in hyps
    assert concl == "R a"


def test_exists_conclusion_stripped():
    t = "∀ (a b : Point), a ≠ b → ∃ L : Line, (a.onLine L) ∧ (b.onLine L)"
    _, _, concl, exists_ = L.split_quantifier_and_arrow(t)
    assert exists_ is True
    assert concl == "(a.onLine L) ∧ (b.onLine L)"


def test_curried_binders_no_forall():
    # helper-style: leading curried binders before the result `:`; split_signature carves them
    header = "(p q : Point) (L : Line) (hpL : p.onLine L) : p.sameSide q L"
    binders_text, type_text = L.split_signature(header)
    assert binders_text == "(p q : Point) (L : Line) (hpL : p.onLine L)"
    assert type_text == "p.sameSide q L"


def test_split_conjuncts_top_level_only():
    region = "distinctPointsOnLine a b AB ∧ (a ≠ b) ∧ ¬(AB.intersectsLine CD)"
    parts = L.split_conjuncts(region)
    assert parts == ["distinctPointsOnLine a b AB", "(a ≠ b)", "¬(AB.intersectsLine CD)"]


def test_parse_binders_objects_and_hyps():
    text = "(a b c : Point) (AB : Line) (h : p.onLine AB)"
    binders = L.parse_binders(text)
    assert binders == [(["a", "b", "c"], "Point"), (["AB"], "Line"), (["h"], "p.onLine AB")]
