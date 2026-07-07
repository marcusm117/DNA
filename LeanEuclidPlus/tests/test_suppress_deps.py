"""@suppress_deps_check — the per-sentence criterion-3 dependency waiver.

Pure-parse tests for `faithful_lib.suppressed_dep_locs_in_src` / `_next_sentence_loc` and their
interaction with `_assumptions_above`. The tag exempts ONE euclid_sentence's cited [Prop.~B.N] from
the dependency check (both Phase-B arms + gate C); a mandatory non-empty reason means it can never
silently mute a real missing dependency. See the SUPPRESS_DEPS_ANNOT block in faithful_lib.py.
"""
import pytest
import faithful_lib as L


def _sent(loc, text="some text", name="step1", body=":= by sorry"):
    return f'  euclid_sentence "{loc}"\n    "{text}"\n    ({name} : True) {body}\n'


# ── happy path ────────────────────────────────────────────────────────────────────────────────────

def test_basic_tag_maps_loc_to_reason():
    src = '  -- @suppress_deps_check "edition typo"\n' + _sent("3.1.2")
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "edition typo"}


def test_no_tag_is_empty():
    src = _sent("3.1.1") + "\n" + _sent("3.1.2", name="step2")
    assert L.suppressed_dep_locs_in_src(src) == {}


def test_multiple_tags_on_different_sentences():
    src = (
        '  -- @suppress_deps_check "typo A"\n' + _sent("3.1.2", name="step2") + "\n"
        + _sent("3.1.3", name="step3") + "\n"
        + '  -- @suppress_deps_check "typo B"\n' + _sent("3.1.5", name="step5")
    )
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "typo A", "3.1.5": "typo B"}


def test_reason_is_stripped():
    src = '  -- @suppress_deps_check "   padded reason   "\n' + _sent("3.1.2")
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "padded reason"}


def test_loc_with_dots_and_multidigit():
    src = '  -- @suppress_deps_check "r"\n' + _sent("12.34.5")
    assert L.suppressed_dep_locs_in_src(src) == {"12.34.5": "r"}


# ── whitespace / grammar tolerance ─────────────────────────────────────────────────────────────────

def test_no_indent_and_tight_spacing():
    src = '--@suppress_deps_check "r"\n' + _sent("3.1.2")
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "r"}


def test_tabs_and_extra_spaces():
    src = '\t--\t @suppress_deps_check   "r"\t\n' + _sent("3.1.2")
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "r"}


# ── interleaving with other annotations ────────────────────────────────────────────────────────────

def test_assumption_lines_between_tag_and_sentence():
    src = (
        '  -- @suppress_deps_check "r"\n'
        '  -- @assumption ("prior fact", a.onLine AB)\n'
        + _sent("3.1.2")
    )
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "r"}


def test_tag_below_assumption_lines_still_attaches():
    # tag directly above the sentence, assumptions above the tag
    src = (
        '  -- @assumption ("prior fact", a.onLine AB)\n'
        '  -- @suppress_deps_check "r"\n'
        + _sent("3.1.2")
    )
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "r"}


def test_args_line_between_tag_and_sentence():
    src = '  -- @suppress_deps_check "r"\n  -- @args: a b AB\n' + _sent("3.1.2")
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "r"}


def test_blank_lines_between_tag_and_sentence():
    src = '  -- @suppress_deps_check "r"\n\n\n' + _sent("3.1.2")
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "r"}


def test_assumptions_above_still_collected_when_suppress_present():
    # the suppress skip in _assumptions_above must not swallow the assumption above it
    src = (
        '  -- @assumption ("prior fact", a.onLine AB)\n'
        '  -- @suppress_deps_check "r"\n'
        + _sent("3.1.2")
    )
    head = src.index("euclid_sentence")
    got = L._assumptions_above(src, head)
    assert got == [("prior fact", "a.onLine AB", None)]


# ── errors: mandatory, well-formed, attached ───────────────────────────────────────────────────────

def test_empty_reason_is_error():
    src = '  -- @suppress_deps_check ""\n' + _sent("3.1.2")
    with pytest.raises(L.FaithfulError, match="non-empty"):
        L.suppressed_dep_locs_in_src(src)


def test_whitespace_only_reason_is_error():
    src = '  -- @suppress_deps_check "   "\n' + _sent("3.1.2")
    with pytest.raises(L.FaithfulError, match="non-empty"):
        L.suppressed_dep_locs_in_src(src)


def test_missing_quotes_is_malformed():
    src = '  -- @suppress_deps_check no quotes here\n' + _sent("3.1.2")
    with pytest.raises(L.FaithfulError, match="malformed"):
        L.suppressed_dep_locs_in_src(src)


def test_unterminated_quote_is_malformed():
    src = '  -- @suppress_deps_check "unterminated\n' + _sent("3.1.2")
    with pytest.raises(L.FaithfulError, match="malformed"):
        L.suppressed_dep_locs_in_src(src)


def test_trailing_junk_after_reason_is_malformed():
    src = '  -- @suppress_deps_check "r" extra junk\n' + _sent("3.1.2")
    with pytest.raises(L.FaithfulError, match="malformed"):
        L.suppressed_dep_locs_in_src(src)


def test_orphan_tag_above_code_is_error():
    src = '  -- @suppress_deps_check "r"\n  euclid_apply (proposition_10 a b AB) as d\n' + _sent("3.1.2")
    with pytest.raises(L.FaithfulError, match="not directly above"):
        L.suppressed_dep_locs_in_src(src)


def test_orphan_tag_at_eof_is_error():
    src = _sent("3.1.1") + '  -- @suppress_deps_check "r"'
    with pytest.raises(L.FaithfulError, match="not directly above"):
        L.suppressed_dep_locs_in_src(src)


def test_orphan_tag_above_structural_sentence_is_error():
    # euclid_wts / euclid_conclude_sentence have no dependency-checked node → tag is meaningless there
    src = '  -- @suppress_deps_check "r"\n  euclid_wts "3.1.6" "I say that F is the center."\n'
    with pytest.raises(L.FaithfulError, match="not directly above"):
        L.suppressed_dep_locs_in_src(src)


# ── things that must NOT trigger ───────────────────────────────────────────────────────────────────

def test_mention_inside_sentence_text_is_not_a_tag():
    # the string only matches at line start after `--`; a mention in prose text must be inert
    src = _sent("3.1.2", text="talk about @suppress_deps_check here")
    assert L.suppressed_dep_locs_in_src(src) == {}


def test_similar_but_different_keyword_ignored():
    src = '  -- @suppress_deps_checked "r"\n' + _sent("3.1.2")
    assert L.suppressed_dep_locs_in_src(src) == {}


def test_two_tags_on_one_sentence_last_wins_no_crash():
    src = '  -- @suppress_deps_check "first"\n  -- @suppress_deps_check "second"\n' + _sent("3.1.2")
    # both resolve to the same loc; last reason wins, and it must not raise
    assert L.suppressed_dep_locs_in_src(src) == {"3.1.2": "second"}


# ── _next_sentence_loc unit behavior ───────────────────────────────────────────────────────────────

def test_next_sentence_loc_skips_annotations():
    src = '  -- @args: a b\n\n' + _sent("9.9.9")
    assert L._next_sentence_loc(src, 0) == "9.9.9"


def test_next_sentence_loc_none_on_code():
    src = '  euclid_apply (proposition_10 a b AB) as d\n' + _sent("9.9.9")
    assert L._next_sentence_loc(src, 0) is None
