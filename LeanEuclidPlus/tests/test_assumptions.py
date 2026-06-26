"""Unit tests for the @assumption / euclid_assumption feature (faithful_lib, check_steps, wired_body)."""
import sys, os, textwrap
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

import faithful_lib as L


# ── helpers ──────────────────────────────────────────────────────────────────

def _parse_assumptions(src):
    """Parse @assumption annotations above the FIRST euclid_sentence in `src`."""
    m = L.SENTENCE_HEAD.search(src)
    assert m, "no euclid_sentence found in test source"
    return L._assumptions_above(src, m.start())


# ── _assumptions_above ───────────────────────────────────────────────────────

def test_assumptions_above_single():
    src = textwrap.dedent("""\
        -- @assumption ("angle B half right", ∠ e:b:c = ∟ / 2)
        euclid_sentence "2.9.16" "..." (step16 : ∠ f:d:b = ∟) := by sorry
    """)
    result = _parse_assumptions(src)
    assert result == [("angle B half right", "∠ e:b:c = ∟ / 2", None)]


def test_assumptions_above_multiple():
    src = textwrap.dedent("""\
        -- @assumption ("angle B half right", ∠ e:b:c = ∟ / 2)
        -- @assumption ("FDB right angle", ∠ f:d:b = ∟)
        euclid_sentence "2.9.16" "..." (step16 : ∠ f:d:b = ∟) := by sorry
    """)
    result = _parse_assumptions(src)
    assert result == [
        ("angle B half right", "∠ e:b:c = ∟ / 2", None),
        ("FDB right angle", "∠ f:d:b = ∟", None),
    ]


def test_assumptions_above_with_override():
    src = textwrap.dedent("""\
        -- @assumption ("AC equals CE", |(a─c)| = |(c─e)|, use_override step2.1)
        euclid_sentence "2.9.19" "..." (step19 : ...) := by sorry
    """)
    result = _parse_assumptions(src)
    assert len(result) == 1
    text, atype, override = result[0]
    assert text == "AC equals CE"
    assert atype == "|(a─c)| = |(c─e)|"
    assert override == "use_override step2.1"


def test_assumptions_above_with_args_coexist():
    """@assumption and @args may both appear above the same sentence."""
    src = textwrap.dedent("""\
        -- @assumption ("AC equals CE", |(a─c)| = |(c─e)|)
        -- @args: a c e
        euclid_sentence "2.9.X" "..." (stepX : ...) := by sorry
    """)
    result = _parse_assumptions(src)
    assert result == [("AC equals CE", "|(a─c)| = |(c─e)|", None)]


def test_assumptions_above_none():
    """A sentence with no @assumption annotation returns None."""
    src = textwrap.dedent("""\
        euclid_sentence "2.9.1" "..." (step1 : ...) := by sorry
    """)
    result = _parse_assumptions(src)
    assert result is None


def test_assumptions_above_stops_at_other_content():
    """Scanning stops immediately at any non-@assumption/non-@args/non-blank line.
    An annotation directly above the sentence IS collected; a non-matching line
    BETWEEN the annotation and the sentence blocks collection entirely."""
    # Case 1: "other comment" is ABOVE the @assumption → annotation is still collected.
    src1 = textwrap.dedent("""\
        -- some other comment
        -- @assumption ("angle B half right", ∠ e:b:c = ∟ / 2)
        euclid_sentence "2.9.16" "..." (step16 : ∠ f:d:b = ∟) := by sorry
    """)
    result1 = _parse_assumptions(src1)
    assert result1 == [("angle B half right", "∠ e:b:c = ∟ / 2", None)]

    # Case 2: "other comment" is BETWEEN the annotation and the sentence → blocks collection.
    src2 = textwrap.dedent("""\
        -- @assumption ("angle B half right", ∠ e:b:c = ∟ / 2)
        -- some other comment
        euclid_sentence "2.9.16" "..." (step16 : ∠ f:d:b = ∟) := by sorry
    """)
    result2 = _parse_assumptions(src2)
    assert result2 is None


# ── parse_helper_objs returns hyp_types ──────────────────────────────────────

def test_parse_helper_objs_returns_type_list(tmp_path):
    """parse_helper_objs returns (objs: list[str], hyp_types: list[str]) not a count."""
    lean = textwrap.dedent("""\
        import SystemE
        set_option linter.unusedVariables false
        set_option linter.unnecessarySeqFocus false
        namespace Elements.Book2
        set_option systemE.solverTime 30 in
        theorem helper_2_99_stepX (a c e : Point)
            (h1 : |(a─c)| = |(c─e)|)
            (h2 : ∠ a:c:e = ∟) :
            |(a─c)| = |(c─e)| := by
          exact h1
        end Elements.Book2
    """)
    f = tmp_path / "stepX.lean"
    f.write_text(lean, encoding="utf-8")
    # Patch prop_num: the file must be under a Prop-folder to extract the number.
    # We use a minimal monkeypatching approach via a temporary directory structure.
    import os
    prop_dir = tmp_path / "Book2" / "Prop99"
    prop_dir.mkdir(parents=True)
    step_file = prop_dir / "stepX.lean"
    step_file.write_text(lean, encoding="utf-8")

    objs, hyp_types = L.parse_helper_objs(str(step_file), 2, "stepX")
    assert objs == ["a", "c", "e"]
    assert hyp_types == ["|(a─c)| = |(c─e)|", "∠ a:c:e = ∟"]


def test_parse_helper_objs_grouped_binders(tmp_path):
    """Grouped binder (h1 h2 : T) expands to two entries of T in hyp_types."""
    lean = textwrap.dedent("""\
        import SystemE
        set_option linter.unusedVariables false
        namespace Elements.Book2
        set_option systemE.solverTime 30 in
        theorem helper_2_99_stepY (a b : Point)
            (h1 h2 : |(a─b)| = |(a─b)|) :
            |(a─b)| = |(a─b)| := h1
        end Elements.Book2
    """)
    prop_dir = tmp_path / "Book2" / "Prop99"
    prop_dir.mkdir(parents=True)
    f = prop_dir / "stepY.lean"
    f.write_text(lean, encoding="utf-8")
    objs, hyp_types = L.parse_helper_objs(str(f), 2, "stepY")
    assert objs == ["a", "b"]
    assert hyp_types == ["|(a─b)| = |(a─b)|", "|(a─b)| = |(a─b)|"]


def test_parse_helper_objs_inline_comment(tmp_path):
    """Inline -- comment after a binder is ignored (blank_comments strips it)."""
    lean = textwrap.dedent("""\
        import SystemE
        set_option linter.unusedVariables false
        namespace Elements.Book2
        set_option systemE.solverTime 30 in
        theorem helper_2_99_stepZ (a c : Point)
            (hassump1 : |(a─c)| = |(a─c)|)   -- "AC equals AC"
            : |(a─c)| = |(a─c)| := hassump1
        end Elements.Book2
    """)
    prop_dir = tmp_path / "Book2" / "Prop99"
    prop_dir.mkdir(parents=True)
    f = prop_dir / "stepZ.lean"
    f.write_text(lean, encoding="utf-8")
    objs, hyp_types = L.parse_helper_objs(str(f), 2, "stepZ")
    assert objs == ["a", "c"]
    assert hyp_types == ["|(a─c)| = |(a─c)|"]


# ── @args remap of hyp types (the bug: show T must use call-site names) ──────

def test_subst_idents_simple_rename():
    out = L._subst_idents("|(c─f)| = |(h─k)|", {"f": "n", "k": "f"})
    assert out == "|(c─n)| = |(h─f)|"          # simultaneous: the new `f` is NOT re-renamed


def test_subst_idents_word_boundary():
    # `c` must not be renamed inside `CF`/`onLine`; only the standalone token.
    out = L._subst_idents("c.onLine CF", {"c": "x"})
    assert out == "x.onLine CF"


def test_subst_idents_keeps_primes_and_subscripts_whole():
    out = L._subst_idents("|(f'─a₁)|", {"f": "ZZ", "a": "YY"})
    assert out == "|(f'─a₁)|"                  # f' and a₁ are single tokens, not f / a


def test_subst_idents_angle_notation():
    out = L._subst_idents("∠ x:y:z = ∠ x:y:z", {"x": "a", "y": "c", "z": "e"})
    assert out == "∠ a:c:e = ∠ a:c:e"


def test_resolve_call_args_remaps_hyp_types(tmp_path):
    """resolve_call_args substitutes the @args object map into the hyp types, so the wired
    `show T` is in call-site names (regression for the @args bug)."""
    lean = textwrap.dedent("""\
        import SystemE
        namespace Elements.Book2
        theorem helper_2_99_stepR (x y z : Point)
            (h : ∠ x:y:z = ∠ x:y:z) :
            ∠ x:y:z = ∠ x:y:z := h
        end Elements.Book2
    """)
    prop_dir = tmp_path / "Book2" / "Prop99"
    prop_dir.mkdir(parents=True)
    (prop_dir / "stepR.lean").write_text(lean, encoding="utf-8")
    node = L.Node("stepR", str(prop_dir / "stepR.lean"), "sentence", "2.99.R",
                  "∠ a:c:e = ∠ a:c:e", "sorry", 0, 0, args=["a", "c", "e"])
    objs, hyp_types = L.resolve_call_args(str(prop_dir), 2, node)
    assert objs == ["a", "c", "e"]
    assert hyp_types == ["∠ a:c:e = ∠ a:c:e"]   # remapped from x:y:z


# ── find_body recognizes the generated wired body (round-trip) ───────────────
# Regression: the generated wired body nests point-pairs `(a─c)` inside the typed hyp slot,
# pushing the call-paren args two levels deep. find_body MUST still classify it as "wired"
# (a fixed-depth regex silently mis-read these → parse_nodes_in_file aborted "not canonical").

def test_find_body_recognizes_euclid_assumption_override_slot():
    body = L.wired_body(2, 99, "step2", ["a", "c", "e"],
                        ["|(a─c)| = |(a─c)|"],
                        [("AC equals AC", "|(a─c)| = |(a─c)|", "use_override step1.1")])
    src = f"    (step2 : |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|) {body}\n"
    sep = src.index(":=")
    state, start, end = L.find_body(src, sep, 2, 99, "step2")
    assert state == "wired"
    assert src[start:end] == body            # span covers the whole call paren, nothing trailing


def test_find_body_recognizes_structural_slot():
    """A non-annotated structural slot `(by euclid_assumption "" (show T; assumption))` is recognized."""
    body = L.wired_body(2, 99, "step3", ["a", "c", "e"],
                        ["|(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|"], None)
    src = f"    (step3 : |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|) {body}\n"
    sep = src.index(":=")
    state, start, end = L.find_body(src, sep, 2, 99, "step3")
    assert state == "wired"
    assert src[start:end] == body


def test_find_body_paren_in_assumption_string_does_not_unbalance():
    """A `(` inside the euclid_assumption text string must not close the call paren early."""
    body = L.wired_body(2, 99, "step2", ["a"],
                        ["|(a─c)| = |(a─c)|"],
                        [("AC (the base) equals AC", "|(a─c)| = |(a─c)|", None)])
    src = f"    (step2 : |(a─c)| = |(a─c)|) {body}\n"
    sep = src.index(":=")
    state, start, end = L.find_body(src, sep, 2, 99, "step2")
    assert state == "wired"
    assert src[start:end] == body


# ── wired_body format ─────────────────────────────────────────────────────────

# Every slot is the ONE fixed shape: (by euclid_assumption "TEXT" (show T; PROOF)).

def test_wired_body_annotated_hyp_plain():
    """Annotated hyp → (by euclid_assumption "text" (show T; assumption))."""
    assumptions = [("AC equals AC", "|(a─c)| = |(a─c)|", None)]
    hyp_types   = ["|(a─c)| = |(a─c)|"]
    body = L.wired_body(2, 99, "step2", ["a", "c", "e"], hyp_types, assumptions)
    assert '(by euclid_assumption "AC equals AC" (show |(a─c)| = |(a─c)|; assumption))' in body
    assert "exact" not in body


def test_wired_body_annotated_hyp_override():
    """Override → (by euclid_assumption "text" (show T; exact pf)) — no `use_override` keyword."""
    assumptions = [("AC equals AC", "|(a─c)| = |(a─c)|", "use_override step1.1")]
    hyp_types   = ["|(a─c)| = |(a─c)|"]
    body = L.wired_body(2, 99, "step2", ["a", "c", "e"], hyp_types, assumptions)
    assert '(by euclid_assumption "AC equals AC" (show |(a─c)| = |(a─c)|; exact step1.1))' in body
    assert "use_override" not in body


def test_wired_body_non_annotated_hyp():
    """Structural hyp → (by euclid_assumption "" (show T; assumption))."""
    hyp_types = ["|(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|"]
    body = L.wired_body(2, 99, "step3", ["a", "c", "e"], hyp_types, None)
    assert '(by euclid_assumption "" (show |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|; assumption))' in body


def test_wired_body_mixed_hyps():
    """Annotated and structural hyps coexist; both in the fixed shape, matched by NORMALIZED TYPE."""
    assumptions = [("AC equals AC", "|(a─c)| = |(a─c)|", None)]
    hyp_types   = ["|(a─c)| = |(a─c)|", "|(c─e)| = |(c─e)|"]
    body = L.wired_body(2, 99, "step_mixed", ["a"], hyp_types, assumptions)
    assert '(by euclid_assumption "AC equals AC" (show |(a─c)| = |(a─c)|; assumption))' in body
    assert '(by euclid_assumption "" (show |(c─e)| = |(c─e)|; assumption))' in body


def test_wired_body_no_assumptions():
    """No annotations → every slot is the structural shape with empty text."""
    hyp_types = ["|(a─c)| = |(c─e)|", "∠ a:c:e = ∟"]
    body = L.wired_body(2, 99, "step_none", ["a", "c", "e"], hyp_types)
    assert '(by euclid_assumption "" (show |(a─c)| = |(c─e)|; assumption))' in body
    assert '(by euclid_assumption "" (show ∠ a:c:e = ∟; assumption))' in body


def test_wired_body_type_normalization():
    """Annotation type is matched after whitespace normalization."""
    assumptions = [("AC equals AC", "|(a─c)|  =  |(a─c)|", None)]
    hyp_types   = ["|(a─c)| = |(a─c)|"]
    body = L.wired_body(2, 99, "step_norm", ["a"], hyp_types, assumptions)
    assert '(by euclid_assumption "AC equals AC" (show |(a─c)| = |(a─c)|; assumption))' in body


def test_wired_body_multiline_type_collapsed_to_one_line():
    """THE regression: a multi-line binder type must be emitted on ONE line (no newline survives),
    so the inline `show` can't be truncated by Lean's indentation rule."""
    hyp_types = ["Triangle.area △ c:d:h + Triangle.area △ c:h:l =\n      Triangle.area △ h:m:f + Triangle.area △ h:f:g"]
    body = L.wired_body(2, 5, "step7", ["c", "d"], hyp_types, None)
    assert "\n" not in body
    assert ("(by euclid_assumption \"\" (show Triangle.area △ c:d:h + Triangle.area △ c:h:l = "
            "Triangle.area △ h:m:f + Triangle.area △ h:f:g; assumption))") in body


# ── check_faithful text-substring via ASSUMPTION_ANNOT ───────────────────────

def test_assumption_annot_regex_basic():
    line = '  -- @assumption ("AC equals AC", |(a─c)| = |(c─e)|)'
    m = L.ASSUMPTION_ANNOT.match(line)
    assert m is not None
    assert m.group(1) == "AC equals AC"
    assert m.group(2).strip() == "|(a─c)| = |(c─e)|"
    assert m.group(3) is None


def test_assumption_annot_regex_with_override():
    line = '  -- @assumption ("AC equals AC", |(a─c)| = |(c─e)|, use_override step2.1)'
    m = L.ASSUMPTION_ANNOT.match(line)
    assert m is not None
    assert m.group(3) == "use_override step2.1"


def test_assumption_annot_regex_conjunctive_type():
    """A type with ∧ (no comma) is correctly captured as field 2."""
    line = '  -- @assumption ("AB right angle", ∠ a:b:c = ∟ ∧ ∠ d:e:f = ∟)'
    m = L.ASSUMPTION_ANNOT.match(line)
    assert m is not None
    assert "∧" in m.group(2)
    assert m.group(3) is None
