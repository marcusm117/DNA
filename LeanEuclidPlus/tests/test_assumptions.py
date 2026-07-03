"""Unit tests for the @assumption / euclid_assumption feature (faithful_lib, check_steps, wired_body)."""
import sys, os, shutil, textwrap
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

import faithful_lib as L
import assumptions as A                    # the ASSUMPTION PHASE script


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


# ── content_sha: @assumption-edits are invisible to the certification manifest ─
# The hash the manifest uses (content_sha) strips `-- @assumption …` lines so a Phase-B reword/drop
# of one (allowed, SOFT per the assumption-latitude policy — it feeds no build) does NOT flip a
# certified node to stale. `@args`, sentence strings, and code MUST still register.

_MAIN = '''\
  -- @assumption ("AF equal to FG", |(a─f)| = |(f─g)|)
  euclid_sentence "2.11.16" "And $FK$ is ... For $AF$ (is) equal to $FG$."
    (step16 : Triangle.area △ f:g:k + Triangle.area △ f:c:k = |(c─f)| * |(f─a)|) := by sorry
'''


def _sha_of(tmp_path, text, name="Main.lean"):
    p = tmp_path / name
    p.write_text(text, encoding="utf-8")
    return L.content_sha(str(p))


def test_content_sha_ignores_assumption_reword(tmp_path):
    """Rewording an @assumption (text AND lean type) does not change content_sha."""
    reworded = _MAIN.replace('("AF equal to FG", |(a─f)| = |(f─g)|)',
                             '("$AF$ equals $FG$", |(f─g)| = |(a─f)|)')
    assert reworded != _MAIN                                   # the bytes really differ
    assert _sha_of(tmp_path, reworded) == _sha_of(tmp_path, _MAIN)


def test_content_sha_ignores_assumption_delete(tmp_path):
    """DELETING the @assumption line normalizes identically to keeping it (whole line + newline
    stripped) — the present↔absent symmetry that a naive blank-out would break."""
    without = _MAIN.split("\n", 1)[1]                         # drop the leading @assumption line + its \n
    assert "@assumption" not in without
    assert _sha_of(tmp_path, without) == _sha_of(tmp_path, _MAIN)


def test_content_sha_registers_args_edit(tmp_path):
    """A `-- @args:` line IS load-bearing for the wire → it must still change the hash."""
    with_args = _MAIN.replace('  euclid_sentence', '  -- @args: a b c\n  euclid_sentence')
    bumped    = with_args.replace('-- @args: a b c', '-- @args: a c e')
    assert _sha_of(tmp_path, bumped) != _sha_of(tmp_path, with_args)


def test_content_sha_registers_claim_edit(tmp_path):
    """A change to the claim type (real code) must still change the hash."""
    edited = _MAIN.replace("|(c─f)| * |(f─a)|", "|(c─f)| * |(f─g)|")
    assert _sha_of(tmp_path, edited) != _sha_of(tmp_path, _MAIN)


def test_content_sha_not_byte_identical_to_file_sha(tmp_path):
    """Sanity: content_sha differs from the raw-byte file_sha when @assumption lines are present
    (so the manifest read/write sides must BOTH use content_sha — they do)."""
    p = tmp_path / "Main.lean"
    p.write_text(_MAIN, encoding="utf-8")
    assert L.content_sha(str(p)) != L.file_sha(str(p))


# ── content_sha: ALL full-line comments are invisible (not just @assumption) ──
# The broadened strip keeps Main comment-edit-immune: editing/adding/deleting ANY full-line `--` comment
# must not flip a certified node to stale. Only `-- @args:`, sentence strings, code, and (deliberately)
# trailing comments still register.

def test_content_sha_ignores_plain_full_line_comment(tmp_path):
    """Adding OR rewording a plain explanatory full-line `--` comment does not change content_sha."""
    with_note    = "  -- h is between a and b\n" + _MAIN
    reworded     = "  -- h lies between a and b (reworded)\n" + _MAIN
    assert with_note != _MAIN and reworded != with_note          # the bytes really differ
    assert _sha_of(tmp_path, with_note) == _sha_of(tmp_path, _MAIN)
    assert _sha_of(tmp_path, reworded)  == _sha_of(tmp_path, _MAIN)


def test_content_sha_registers_trailing_comment(tmp_path):
    """A TRAILING `--` comment is NOT stripped (full-line anchor) — it stays in the hash. This is the
    deliberate limitation that the Main `own-line-only` gate exists to forbid."""
    a = _MAIN + "  euclid_finish -- variant a\n"
    b = _MAIN + "  euclid_finish -- variant b\n"
    assert _sha_of(tmp_path, a) != _sha_of(tmp_path, b)


# ── _trailing_comment_lineno ──────────────────────────────────────────────────

def test_trailing_comment_lineno_flags_real_trailing():
    assert L._trailing_comment_lineno("x := by sorry -- note") == [1]


def test_trailing_comment_lineno_ignores_full_line_comment():
    assert L._trailing_comment_lineno("  -- a whole-line note") == []
    assert L._trailing_comment_lineno("-- @args: a c e") == []


def test_trailing_comment_lineno_ignores_dashes_inside_sentence_string():
    """The `--` inside a euclid_sentence string (e.g. `cut---equally`) is NOT a comment."""
    line = '  euclid_sentence "If a straight line be cut---equally" "2.5.1" (s : T) := by sorry'
    assert L._trailing_comment_lineno(line) == []


def test_trailing_comment_lineno_flags_trailing_after_a_string():
    """A real trailing comment AFTER a (closed) string is still flagged."""
    line = '  euclid_sentence "cut---equally" "2.5.1" (s : T) := by sorry  -- real trailing'
    assert L._trailing_comment_lineno(line) == [1]


def test_trailing_comment_lineno_multiline_reports_each():
    src = ('  euclid_intros\n'
           '  euclid_finish -- bad\n'
           '  -- fine full line\n'
           '  exact h -- also bad\n')
    assert L._trailing_comment_lineno(src) == [2, 4]


# ── integrity_scan: Main.lean hygiene gates (no @args, comments own-line only) ─
# Built under the REAL Book-tree (Book9/Prop2) because integrity_scan derives the book number from the
# path relative to BOOK_ROOT and globs the prop folder. Torn down after. Other structural problems
# (missing backing file / cap) may also be reported — we assert only on the two Main-gate substrings.

_HYG_MAIN = ('import SystemE\n'
             'namespace Elements.Book2\n'
             'theorem proposition_2 : True := by\n'
             '  euclid_sentence "9.2.1" "Some sentence." (step1 : True) := by sorry\n'
             'end Elements.Book2\n')


def _make_hyg_prop(main_src, extra=None):
    """Write Book9/Prop2/Main.lean (+ optional {relname: src} backing files) under BOOK_ROOT."""
    propdir = os.path.join(L.BOOK_ROOT, "Book9", "Prop2")
    os.makedirs(propdir, exist_ok=True)
    with open(os.path.join(propdir, "Main.lean"), "w", encoding="utf-8") as f:
        f.write(main_src)
    for name, src in (extra or {}).items():
        with open(os.path.join(propdir, name), "w", encoding="utf-8") as f:
            f.write(src)
    return propdir


def _rm_hyg_prop():
    shutil.rmtree(os.path.join(L.BOOK_ROOT, "Book9"), ignore_errors=True)


def test_integrity_scan_bans_args_in_main():
    src = _HYG_MAIN.replace('  euclid_sentence "9.2.1"',
                            '  -- @args: a c e\n  euclid_sentence "9.2.1"')
    propdir = _make_hyg_prop(src)
    try:
        problems = L.integrity_scan(propdir)
        assert any("BANNED in Main" in p for p in problems), problems
    finally:
        _rm_hyg_prop()


def test_integrity_scan_flags_trailing_comment_in_main():
    src = _HYG_MAIN.replace(':= by sorry', ':= by sorry  -- a trailing note')
    propdir = _make_hyg_prop(src)
    try:
        problems = L.integrity_scan(propdir)
        assert any("TRAILING" in p for p in problems), problems
    finally:
        _rm_hyg_prop()


def test_integrity_scan_clean_main_no_hygiene_problems():
    propdir = _make_hyg_prop(_HYG_MAIN)
    try:
        problems = L.integrity_scan(propdir)
        assert not any("BANNED in Main" in p for p in problems), problems
        assert not any("TRAILING" in p for p in problems), problems
    finally:
        _rm_hyg_prop()


def test_integrity_scan_args_in_backing_file_not_flagged_as_main():
    """`@args` in a BACKING file is legitimate (load-bearing on a sub-node) — the Main-only gate must
    NOT flag it. (Other problems may be reported; just not the Main `@args` ban.)"""
    step = ('-- @args: a c e\n'
            'have sub1 : True := by sorry\n')
    propdir = _make_hyg_prop(_HYG_MAIN, extra={"step1.lean": step})
    try:
        problems = L.integrity_scan(propdir)
        assert not any("BANNED in Main" in p for p in problems), problems
    finally:
        _rm_hyg_prop()


# ══════════════════════════════════════════════════════════════════════════════
# ASSUMPTION PHASE (scripts/assumptions.py + faithful_lib helpers)
# ══════════════════════════════════════════════════════════════════════════════

# ── classify_target (pure; distinct from classify_smell — tolerates other-node sorries) ──

def test_classify_target_closes():
    # build ok + only sorry WARNINGS (other nodes) ⟹ the target's euclid_finish discharged
    assert A.classify_target(True, "warning: declaration uses 'sorry'") == "closes"

def test_classify_target_hard():
    assert A.classify_target(False, "error: ... Could not prove the goal ...") == "hard"

def test_classify_target_sat():
    assert A.classify_target(False, "Prover returned SAT") == "sat"

def test_classify_target_wall():
    assert A.classify_target(False, "build of X exceeded 45s wall clock — TOO BIG") == "wall"

def test_classify_target_crash():
    out = "libleanshared.so(l_Lean_Elab_Tactic_evalTactic+0x1)\nerror: Lean exited with code 1"
    assert A.classify_target(False, out) == "crash"

def test_classify_target_error():
    assert A.classify_target(False, "error: unexpected token") == "error"


# ── _frame_hint (STEP A fail-closed guidance) ──

def test_frame_hint_points_at_wlog_when_generalizing_present():
    hint = A._frame_hint("  wlog h : P generalizing b c with Hsym\n")
    assert "wlog" in hint and "Hsym" in hint and "do NOT delete" in hint

def test_frame_hint_generic_when_no_generalizing():
    hint = A._frame_hint("  euclid_intros\n")
    assert "do NOT delete" in hint and "generalizing" not in hint


# ── materialize / sentence_blocks (pure string transform) ──

def test_materialize_inserts_have_above_assumption_block():
    src = ('  euclid_intros\n'
           '  -- @assumption ("AB eq DE", |(a─b)| = |(d─e)|)\n'
           '  euclid_sentence "1.4.1" "..." (step1 : ptImg b = e) := by sorry\n')
    out = A.materialize(src)
    assert "  have step1_assumption1 : |(a─b)| = |(d─e)| := by sorry" in out
    # the @assumption block stays contiguous ABOVE the sentence, so _assumptions_above still works
    m = L.SENTENCE_HEAD.search(out)
    assert L._assumptions_above(out, m.start()) == [("AB eq DE", "|(a─b)| = |(d─e)|", None)]


def test_materialize_matches_nested_indent():
    """A sentence inside a 4-space reductio block gets its have at 4-space indent (else it breaks
    Lean's block structure)."""
    src = ('  have habsurd : X := by\n'
           '    intro hne\n'
           '    -- @assumption ("AB neq AC", |(a─b)| ≠ |(a─c)|)\n'
           '    euclid_sentence "1.6.1" "..." (step1 : Y) := by sorry\n')
    out = A.materialize(src)
    assert "    have step1_assumption1 : |(a─b)| ≠ |(a─c)| := by sorry" in out


def test_materialize_every_assumption_gets_a_have():
    """Two @assumptions on one sentence → two haves (no exceptions)."""
    src = ('  -- @assumption ("t1", T1)\n'
           '  -- @assumption ("t2", T2)\n'
           '  euclid_sentence "1.1.1" "..." (step1 : X) := by sorry\n')
    out = A.materialize(src)
    assert "have step1_assumption1 : T1 := by sorry" in out
    assert "have step1_assumption2 : T2 := by sorry" in out


def test_apply_verdicts_valid_and_gap_bodies():
    """STEP B (apply_verdicts) sets each materialized have's body + tag IN PLACE."""
    src = A.materialize('  -- @assumption ("t", T1)\n'
                        '  euclid_sentence "1.1.1" "..." (step1 : X) := by sorry\n')
    valid = A.apply_verdicts(src, {"step1_assumption1": {"status": "valid"}})
    assert "-- @assumption_valid" in valid
    assert "have step1_assumption1 : T1 := by euclid_finish" in valid
    gap = A.apply_verdicts(src, {"step1_assumption1": {"status": "gap"}})
    assert "-- @assumption_gap" in gap
    assert "have step1_assumption1 : T1 := by sorry" in gap


def test_apply_verdicts_ladder_body_and_import():
    """A valid record persists its WINNING tactic as the body; a tactic needing an import gets that import
    added to Main; cheap rungs add nothing."""
    src = A.materialize('import SystemE\n'
                        '  -- @assumption ("t", T1)\n'
                        '  euclid_sentence "1.1.1" "..." (step1 : X) := by sorry\n')
    rfl_body = A.apply_verdicts(src, {"step1_assumption1": {"status": "valid", "tactic": "rfl"}})
    assert "have step1_assumption1 : T1 := by rfl" in rfl_body
    assert "import Mathlib.Tactic.Linarith" not in rfl_body
    lin_body = A.apply_verdicts(src, {"step1_assumption1":
                                      {"status": "valid", "tactic": "linarith",
                                       "import": "Mathlib.Tactic.Linarith"}})
    assert "have step1_assumption1 : T1 := by linarith" in lin_body
    assert "import Mathlib.Tactic.Linarith" in lin_body


def test_apply_verdicts_idempotent_tag():
    """Running apply_verdicts twice doesn't stack tag comments (idempotent replace)."""
    src = A.materialize('  -- @assumption ("t", T1)\n'
                        '  euclid_sentence "1.1.1" "..." (step1 : X) := by sorry\n')
    once = A.apply_verdicts(src, {"step1_assumption1": {"status": "valid"}})
    twice = A.apply_verdicts(once, {"step1_assumption1": {"status": "valid"}})
    assert twice.count("-- @assumption_valid") == 1
    assert twice == once


# ── assumption_current_tags / count_inline_assumption_haves (body-state derivation) ──

def test_assumption_current_tags(tmp_path):
    main = tmp_path / "Main.lean"
    main.write_text('  have step1_assumption1 : T := by euclid_finish\n'
                    '  have step2_assumption1 : T := by sorry\n'
                    '  have step3_assumption1 : T := by euclid_apply (helper_1_1_step3_assumption1 a)\n'
                    '  have step4_assumption1 : T := by rfl\n'
                    '  have step5_assumption1 : T := by linarith\n'
                    '  have step6_assumption1 : T := by simp (config := { zetaDelta := true })\n',
                    encoding="utf-8")
    assert L.assumption_current_tags(str(main)) == {
        "step1_assumption1": "valid",     # inline euclid_finish
        "step2_assumption1": "gap",       # sorry
        "step3_assumption1": "gap",       # wired backing call (stable through Phase C)
        "step4_assumption1": "valid",     # inline rfl (ladder closer)
        "step5_assumption1": "valid",     # inline linarith (ladder closer)
        "step6_assumption1": "valid",     # inline simp (ladder closer; `simp\\b` ≠ `simp_all`)
    }
    assert L.count_inline_assumption_haves(str(main)) == 4


# ── assumption_structure_problems: #3 PARITY + #1 FORCE (Book9/Prop2 fixture) ──

_ASSUMP_MAIN_NO_HAVE = ('import SystemE\n'
                        'namespace Elements.Book2\n'
                        'theorem proposition_2 : True := by\n'
                        '  -- @assumption ("AC eq CE", |(a─c)| = |(c─e)|)\n'
                        '  euclid_sentence "9.2.1" "S." (step1 : True) := by sorry\n'
                        'end Elements.Book2\n')

# helper_<book>_<prop>_step1 — book=9 (from the Book9 PATH), prop=2 (Prop2). Takes the assumption type.
_ASSUMP_STEP1_WITH_BINDER = ('import SystemE\n'
                             'namespace Elements.Book2\n'
                             'theorem helper_9_2_step1 (a c e : Point) (h : |(a─c)| = |(c─e)|) : True '
                             ':= trivial\n'
                             'end Elements.Book2\n')

_ASSUMP_STEP1_NO_BINDER = ('import SystemE\n'
                           'namespace Elements.Book2\n'
                           'theorem helper_9_2_step1 (a c e : Point) : True := trivial\n'
                           'end Elements.Book2\n')


def test_assumption_parity_flags_missing_have():
    """#3 PARITY: a sentence with an @assumption but no materialized have is flagged."""
    propdir = _make_hyg_prop(_ASSUMP_MAIN_NO_HAVE, extra={"step1.lean": _ASSUMP_STEP1_WITH_BINDER})
    try:
        problems = L.assumption_structure_problems(propdir)
        assert any("step1_assumption1` is missing" in p for p in problems), problems
    finally:
        _rm_hyg_prop()


def test_assumption_parity_ok_with_have():
    """With the have materialized (real materialize layout — have ABOVE the @assumption block, so
    _assumptions_above still finds it), PARITY passes and FORCE passes (binder present)."""
    main = A.apply_verdicts(A.materialize(_ASSUMP_MAIN_NO_HAVE), {"step1_assumption1": {"status": "valid"}})
    propdir = _make_hyg_prop(main, extra={"step1.lean": _ASSUMP_STEP1_WITH_BINDER})
    try:
        problems = L.assumption_structure_problems(propdir)
        assert problems == [], problems
    finally:
        _rm_hyg_prop()


def test_assumption_force_flags_missing_binder():
    """#1 FORCE: the assumption type must be a hyp binder of the sentence's helper — no exceptions."""
    main = A.apply_verdicts(A.materialize(_ASSUMP_MAIN_NO_HAVE), {"step1_assumption1": {"status": "valid"}})
    propdir = _make_hyg_prop(main, extra={"step1.lean": _ASSUMP_STEP1_NO_BINDER})
    try:
        problems = L.assumption_structure_problems(propdir)
        assert any("not a hypothesis binder" in p for p in problems), problems
    finally:
        _rm_hyg_prop()
