"""extract_facts — symbol × role × polarity over hypothesis/conclusion regions."""
import faithful_lib as L


def _syms(facts, role=None, polarity=None):
    return sorted(f["symbol"] for f in facts
                  if (role is None or f["role"] == role)
                  and (polarity is None or f["polarity"] == polarity))


def test_negation_makes_neg_polarity():
    facts = L.extract_facts("¬(a.onCircle α)", "concl")
    assert facts == [{"symbol": "onCircle", "role": "concl", "polarity": "neg",
                      "raw": "¬(a.onCircle α)", "via": None}]


def test_ne_is_ne_neg_even_inside_parens():
    # `(a ≠ b)` must yield a `ne`/neg fact (regression: comparator was missed inside parens)
    facts = L.extract_facts("(a ≠ b) ∧ (a ≠ c)", "concl")
    assert _syms(facts) == ["ne", "ne"]
    assert all(f["symbol"] == "ne" and f["polarity"] == "neg" for f in facts)


def test_opaque_method_matched_not_abbrev_substring():
    # `\bonLine\b` matches `a.onLine` but NOT the abbrev `distinctPointsOnLine` (capital O in the abbrev)
    facts = L.extract_facts("a.onLine L", "hyp")
    assert _syms(facts) == ["onLine"]
    facts2 = L.extract_facts("distinctPointsOnLine a b L", "hyp")
    assert "distinctPointsOnLine" in _syms(facts2)
    # but the unfold ALSO contributes onLine atoms (via the abbrev)
    assert any(f["symbol"] == "onLine" and f["via"] == "distinctPointsOnLine" for f in facts2)


def test_metric_right_angle_emits_three_symbols():
    # `∠ f:b:c = ∟` → angle + right_angle + eq, all same role/polarity
    facts = L.extract_facts("∠ f:b:c = ∟", "hyp")
    assert _syms(facts) == ["angle", "eq", "right_angle"]
    assert all(f["polarity"] == "pos" for f in facts)


def test_right_angle_not_misread_as_angle_only():
    facts = L.extract_facts("∠ f:b:c = ∟", "concl")
    assert "right_angle" in _syms(facts)
    assert "angle" in _syms(facts)


def test_length_inequality():
    facts = L.extract_facts("|(a─c)| < |(a─b)|", "hyp")
    assert "length" in _syms(facts)
    assert "lt" in _syms(facts)


def test_intersectsLine_negation_polarity():
    facts = L.extract_facts("¬(AB.intersectsLine CD)", "hyp")
    assert facts == [{"symbol": "intersectsLine", "role": "hyp", "polarity": "neg",
                      "raw": "¬(AB.intersectsLine CD)", "via": None}]
