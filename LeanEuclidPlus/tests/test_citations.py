"""cited_in_body — euclid_apply head names (props / constructions / helpers), deduped, comment-safe."""
import faithful_lib as L


def test_pulls_prop_and_construction_heads():
    body = """
  euclid_intros
  euclid_apply (proposition_30 L M L)
  euclid_apply (line_from_points p q) as PQ
  euclid_finish
"""
    assert L.cited_in_body(body) == ["proposition_30", "line_from_points"]


def test_dedup_preserves_first_order():
    body = "euclid_apply (proposition_5 a) ; euclid_apply (proposition_5 b) ; euclid_apply (helper_2_1_step1 c)"
    assert L.cited_in_body(body) == ["proposition_5", "helper_2_1_step1"]


def test_commented_apply_is_ignored():
    body = """
  -- euclid_apply (proposition_99 x)   was the old approach
  euclid_apply (proposition_31 g b c BC) as GH
"""
    assert L.cited_in_body(body) == ["proposition_31"]


def test_namespace_qualified_head_stripped_to_decl_name():
    # regression: a fully-qualified head like `Elements.Book1.proposition_46` must record the DECL name
    # `proposition_46`, NOT the namespace prefix `Elements`.
    body = """
  euclid_apply (Elements.Book1.proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_apply (Elements.Book1.proposition_31 c a d AD) as CF
  euclid_apply (line_from_points p q) as PQ
"""
    cites = L.cited_in_body(body)
    assert "Elements" not in cites                       # the prefix must never leak in
    assert cites == ["proposition_46", "proposition_31", "line_from_points"]


def test_qualified_and_bare_collapse_to_same_name():
    # the qualified form and the bare form record the SAME name, so `--cites proposition_5` matches both
    body = "euclid_apply (Elements.Book1.proposition_5 a) ; euclid_apply (proposition_5 b)"
    assert L.cited_in_body(body) == ["proposition_5"]
