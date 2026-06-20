"""find.py — filter logic (matches/step_allowed/parse_args) AND the full main() command path.

The main() integration tests are the coverage that was missing when the standalone --steps/--steps-all
crash shipped: they run find.main() exactly as the CLI does (monkeypatching the bake away to fixed
fixture rows) and assert stdout + exit code."""
import bake_index as B
import find as F
from conftest import fixture


def _rows():
    rows = []
    for fx in ("axiom_neg.lean", "construction_exists.lean", "helper_curried.lean", "prop_family.lean"):
        rows.extend(B.parse_file(fixture(fx)))
    return rows


def _opts(**kw):
    base = {k.lstrip("-").replace("-", "_"): None for k in F._SINGLE_FLAGS}
    base.update({k.lstrip("-").replace("-", "_"): [] for k in F._MULTI_FLAGS})
    base.update({k.lstrip("-").replace("-", "_"): False for k in F._BARE_FLAGS})
    # multi flags are LISTS; allow a test to pass a bare string and wrap it (convenience)
    multi_keys = {k.lstrip("-").replace("-", "_") for k in F._MULTI_FLAGS}
    for k, v in kw.items():
        base[k] = [v] if (k in multi_keys and isinstance(v, str)) else v
    return base


def _names(rows, opts):
    return sorted(r["name"] for r in rows if F.matches(r, opts))


def test_concludes_filter():
    rows = _rows()
    # proposition_5 concludes ∠ a:b:c = ∠ a:c:b → an `angle`/`eq` conclusion
    got = _names(rows, _opts(concludes="angle"))
    assert "proposition_5" in got
    # between_symm does NOT conclude an angle
    assert "between_symm" not in got


def test_consumes_filter():
    rows = _rows()
    got = _names(rows, _opts(consumes="formParallelogram"))
    assert got == ["sample_helper"]


def test_mentions_any_role():
    rows = _rows()
    got = _names(rows, _opts(mentions="onLine"))
    assert "line_from_points" in got            # concl (∃ body)
    assert "sample_helper" in got               # hyp


def test_polarity_query_prefix():
    rows = _rows()
    # ¬intersectsLine as a hyp → only sample_helper (its `¬(M.intersectsLine L)`); NOT intersection_lines
    # (whose hyp is the POSITIVE `L.intersectsLine M`).
    neg = _names(rows, _opts(consumes="¬intersectsLine"))
    assert "sample_helper" in neg
    assert "intersection_lines" not in neg
    # no polarity prefix ⟹ either polarity matches → both the positive and negative consumers appear
    either = _names(rows, _opts(consumes="intersectsLine"))
    assert "sample_helper" in either and "intersection_lines" in either


def test_kind_comma_list_and_and_combination():
    rows = _rows()
    # AND: kind ∈ {axiom,prop} AND mentions `ne`. between_symm & line_from_points are axioms with `ne`.
    got = _names(rows, _opts(kind="axiom,prop", mentions="ne"))
    assert "between_symm" in got
    assert "line_from_points" in got
    # narrowing kind to just `prop` drops the axioms (none of the prop fixtures has a bare `ne`)
    assert "between_symm" not in _names(rows, _opts(kind="prop", mentions="ne"))
    # helper kind is excluded by the kind filter even though sample_helper has facts
    assert "sample_helper" not in got


def test_multi_symbol_is_AND_via_parse_args():
    # parse_args: repeated/comma-listed symbol flags accumulate into a LIST (no silent overwrite — the bug)
    o = F.parse_args(["--consumes", "formParallelogram", "--consumes", "onLine"])
    assert o["consumes"] == ["formParallelogram", "onLine"]
    o2 = F.parse_args(["--consumes", "formParallelogram,onLine"])
    assert o2["consumes"] == ["formParallelogram", "onLine"]


def test_multi_symbol_matches_require_all():
    rows = [
        {"kind": "axiom", "name": "both", "source": "Book/Prop01.lean:1", "signature": "x", "docstring": "",
         "cited_props": [], "facts": [{"symbol": "formParallelogram", "role": "hyp", "polarity": "pos", "raw": "", "via": None},
                                      {"symbol": "onLine", "role": "hyp", "polarity": "pos", "raw": "", "via": None}]},
        {"kind": "axiom", "name": "only_one", "source": "Book/Prop02.lean:1", "signature": "x", "docstring": "",
         "cited_props": [], "facts": [{"symbol": "formParallelogram", "role": "hyp", "polarity": "pos", "raw": "", "via": None}]},
    ]
    got = _names(rows, _opts(consumes=["formParallelogram", "onLine"]))
    assert got == ["both"]                                       # AND: needs BOTH symbols


def test_cites_filter():
    rows = _rows()
    assert _names(rows, _opts(cites="proposition_5")) == ["proposition_5'"]


def test_name_glob():
    rows = _rows()
    assert sorted(_names(rows, _opts(name="proposition_5*"))) == ["proposition_5", "proposition_5'"]


def test_grep_docstring():
    rows = _rows()
    got = _names(rows, _opts(grep="symmetry"))
    assert got == ["between_symm"]


# ── location parsers + book/prop filter ──────────────────────────────────────────────────────────────
def test_book_and_prop_of_source_paths():
    assert F._book_of({"source": "Book/Prop05.lean:7"}) == 1            # Book/ (no digit) → book 1
    assert F._book_of({"source": "Book2/Prop01/Main.lean:22"}) == 2
    assert F._book_of({"source": "Book2/Prop05/step5.lean:9"}) == 2
    assert F._book_of({"source": "SystemE/Theory/Inferences/Metric.lean:3"}) is None
    assert F._book_of({"source": "Helpers/SameSide.lean:17"}) is None

    assert F._prop_of({"source": "Book/Prop05.lean:7"}) == 5
    assert F._prop_of({"source": "Book2/Prop01/Main.lean:22"}) == 1
    assert F._prop_of({"source": "Book2/Prop05/step5.lean:9"}) == 5
    assert F._prop_of({"source": "SystemE/Theory/Inferences/Metric.lean:3"}) is None


def test_book_filter_splits_the_two_prop_1s():
    rows = [{"kind": "prop", "name": "proposition_1", "source": "Book/Prop01.lean:5", "facts": []},
            {"kind": "prop", "name": "proposition_1", "source": "Book2/Prop01/Main.lean:22", "facts": []}]
    b1 = [r for r in rows if F.matches(r, _opts(name="proposition_1", book="1"))]
    b2 = [r for r in rows if F.matches(r, _opts(name="proposition_1", book="2"))]
    assert [r["source"] for r in b1] == ["Book/Prop01.lean:5"]
    assert [r["source"] for r in b2] == ["Book2/Prop01/Main.lean:22"]


def test_prop_and_book_prop_combo():
    rows = [{"kind": "prop", "name": "proposition_5", "source": "Book/Prop05.lean:7", "facts": []},
            {"kind": "step", "name": "helper_2_5_step1", "source": "Book2/Prop05/step1.lean:9", "facts": []},
            {"kind": "prop", "name": "proposition_6", "source": "Book2/Prop06/Main.lean:1", "facts": []}]
    # --prop 5 (no book) matches BOTH books' prop 5 material
    p5 = {r["name"] for r in rows if F.matches(r, _opts(prop="5")) and F.step_allowed(r, _opts(prop="5"))}
    assert p5 == {"proposition_5"}                              # step hidden without --steps/--kind step
    # --book 2 --prop 5 --steps → the Book2 Prop05 step
    o = _opts(prop="5", book="2", steps=True)
    got = {r["name"] for r in rows if F.matches(r, o) and F.step_allowed(r, o)}
    assert got == {"helper_2_5_step1"}


def test_int_opt_rejects_non_numeric():
    import pytest
    with pytest.raises(ValueError):
        F._int_opt(_opts(book="foo"), "book")
    assert F._int_opt(_opts(book="2"), "book") == 2
    assert F._int_opt(_opts(book=None), "book") is None


# ── step gating ───────────────────────────────────────────────────────────────────────────────────────
def test_step_allowed_default_hides_then_opt_in():
    step = {"kind": "step", "source": "Book2/Prop01/step1.lean:9", "name": "helper_2_1_step1"}
    other = {"kind": "prop", "source": "Book/Prop05.lean:1", "name": "proposition_5"}
    assert F.step_allowed(other, _opts()) is True                  # non-step always allowed
    assert F.step_allowed(step, _opts()) is False                  # hidden by default
    assert F.step_allowed(step, _opts(steps=True)) is True          # --steps widens
    assert F.step_allowed(step, _opts(kind="step")) is True         # --kind step implies visibility
    assert F.step_allowed(step, _opts(kind="prop,step")) is True    # in a comma-list too


def test_parse_args_value_and_bare():
    opts = F.parse_args(["--concludes", "angle", "--kind", "prop", "--json"])
    assert opts["concludes"] == ["angle"]                       # multi flag → list
    assert opts["kind"] == "prop"                               # single flag → str
    assert opts["json"] is True


def test_parse_args_book_value_and_steps_bare():
    opts = F.parse_args(["--book", "2", "--prop", "5", "--steps"])
    assert opts["book"] == "2" and opts["prop"] == "5" and opts["steps"] is True


def test_parse_args_rejects_unknown_and_steps_all_gone():
    import pytest
    with pytest.raises(ValueError):
        F.parse_args(["--steps-all"])                              # removed flag is now unknown
    with pytest.raises(ValueError):
        F.parse_args(["--bogus"])


# ── full main() command path (the coverage that was missing) ────────────────────────────────────────────
# Synthetic rows with REAL-looking source paths (the fixtures' own source is tests/fixtures/…, which has
# no Book*/Prop* segment — fine for symbol filters, but book/prop filtering needs real paths). These
# carry the fixtures' citation/docstring data where a test needs it.
def _main_rows():
    return [
        {"kind": "prop", "name": "proposition_5", "source": "Book/Prop05.lean:7",
         "signature": "∀ …, ∠ a:b:c = ∠ a:c:b", "docstring": "", "facts": [], "cited_props": []},
        {"kind": "prop", "name": "proposition_5'", "source": "Book/Prop05.lean:26",
         "signature": "∀ …", "docstring": "", "facts": [], "cited_props": ["proposition_5"]},
        {"kind": "prop", "name": "proposition_1", "source": "Book2/Prop01/Main.lean:22",
         "signature": "∀ …", "docstring": "", "facts": [], "cited_props": []},
        {"kind": "step", "name": "helper_2_1_step1", "source": "Book2/Prop01/step1.lean:9",
         "signature": "∠ f:b:c = ∟", "docstring": "", "facts": [], "cited_props": []},
        {"kind": "step", "name": "helper_2_5_step1", "source": "Book2/Prop05/step1.lean:9",
         "signature": "x", "docstring": "", "facts": [], "cited_props": []},
    ]


def _run(monkeypatch, capsys, argv):
    """Run find.main(argv) with the bake replaced by fixed rows; return (exit_code, stdout)."""
    rows = _main_rows()
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    code = F.main(argv)
    return code, capsys.readouterr().out


def test_main_bare_steps_errors_and_points_to_kind_step(monkeypatch, capsys):
    code, out = _run(monkeypatch, capsys, ["--steps"])
    assert code == 2
    assert "no selector given" in out
    assert "--kind step" in out                                    # the guidance the user asked for


def test_main_kind_step_lists_steps(monkeypatch, capsys):
    code, out = _run(monkeypatch, capsys, ["--kind", "step"])
    assert code == 0
    assert "helper_2_1_step1" in out and "helper_2_5_step1" in out
    assert "match(es)" in out


def test_main_default_hides_steps(monkeypatch, capsys):
    # a selector that WOULD match a step's kind only via --steps: here use --name on a step
    code, out = _run(monkeypatch, capsys, ["--name", "helper_2_1_step1"])
    assert code == 0
    assert "no matches" in out                                     # step hidden without --steps/--kind step
    code2, out2 = _run(monkeypatch, capsys, ["--name", "helper_2_1_step1", "--steps"])
    assert "helper_2_1_step1" in out2                              # --steps reveals it


def test_main_book_filter(monkeypatch, capsys):
    c1, o1 = _run(monkeypatch, capsys, ["--book", "1", "--name", "proposition_5"])
    assert "Book/Prop05.lean" in o1 and "Book2/" not in o1
    c2, o2 = _run(monkeypatch, capsys, ["--book", "2", "--kind", "step"])
    assert "helper_2_1_step1" in o2 and "helper_2_5_step1" in o2


def test_main_prop_filter(monkeypatch, capsys):
    _, out = _run(monkeypatch, capsys, ["--prop", "5", "--kind", "step"])
    assert "helper_2_5_step1" in out and "helper_2_1_step1" not in out


def test_main_bad_book_value_exits_2(monkeypatch, capsys):
    code, out = _run(monkeypatch, capsys, ["--book", "foo", "--name", "x"])
    assert code == 2 and "takes a NUMBER" in out


def test_main_depends_of_mode(monkeypatch, capsys):
    code, out = _run(monkeypatch, capsys, ["--depends-of", "proposition_5'"])
    assert code == 0
    assert "proposition_5" in out                                  # prints its cited_props
    assert "Book/Prop05.lean:7" in out                             # …WITH the cited decl's location


def test_main_depends_of_resolves_each_citation_location(monkeypatch, capsys):
    # a citer whose deps resolve to (a) one source, (b) TWO sources (same name in both books),
    # (c) a name absent from the index.
    rows = [
        {"kind": "prop", "name": "citer", "source": "Book2/Prop09/Main.lean:1", "facts": [],
         "cited_props": ["proposition_5", "only_once", "ghost_decl"]},
        {"kind": "prop", "name": "proposition_5", "source": "Book/Prop05.lean:7", "facts": [], "cited_props": []},
        {"kind": "prop", "name": "proposition_5", "source": "Book2/Prop05/Main.lean:34", "facts": [], "cited_props": []},
        {"kind": "axiom", "name": "only_once", "source": "SystemE/Theory/Inferences/X.lean:3", "facts": [], "cited_props": []},
    ]
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    code = F.main(["--depends-of", "citer"])
    out = capsys.readouterr().out
    assert code == 0
    # (a) single source resolves cleanly
    assert "only_once" in out and "SystemE/Theory/Inferences/X.lean:3" in out
    # (b) a name in two books shows BOTH sources, separated by ' | '
    assert "Book/Prop05.lean:7" in out and "Book2/Prop05/Main.lean:34" in out
    assert "|" in out
    # (c) an unknown citation is flagged, not silently dropped
    assert "ghost_decl" in out and "(not indexed)" in out


def test_main_depends_of_unknown(monkeypatch, capsys):
    code, out = _run(monkeypatch, capsys, ["--depends-of", "nope_not_here"])
    assert code == 1 and "no declaration named" in out


def test_main_json_output(monkeypatch, capsys):
    import json
    code, out = _run(monkeypatch, capsys, ["--name", "proposition_5", "--json"])
    assert code == 0
    data = json.loads(out)
    assert any(r["name"] == "proposition_5" for r in data)


def test_main_no_match_exit_0(monkeypatch, capsys):
    code, out = _run(monkeypatch, capsys, ["--name", "does_not_exist"])
    assert code == 0 and "no matches" in out


def test_main_unknown_flag_exit_2(monkeypatch, capsys):
    code, out = _run(monkeypatch, capsys, ["--bogus"])
    assert code == 2


# ── symbol aliases + validation (Follow-up Fix 3) ──────────────────────────────────────────────────────
def _facts_rows():
    """Rows with REAL signatures + facts, so --concludes/--consumes match and projection has regions."""
    return [
        {"kind": "axiom", "name": "parallelogram_area",
         "source": "SystemE/Theory/Inferences/Transfer.lean:189",
         "signature": "∀ (a b c d : Point) (AB CD AC BD : Line), formParallelogram a b c d AB CD AC BD → "
                      "Triangle.area △ a:c:d + Triangle.area △ a:d:b = Triangle.area △ b:a:c",
         "docstring": "splits a parallelogram along its diagonals",
         "facts": [{"symbol": "formParallelogram", "role": "hyp", "polarity": "pos", "raw": "", "via": None},
                   {"symbol": "area", "role": "concl", "polarity": "pos", "raw": "", "via": None}],
         "cited_props": []},
        {"kind": "prop", "name": "proposition_11", "source": "Book/Prop11.lean:8",
         "signature": "∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∠ f:a:b = ∟",
         "docstring": "erect a perpendicular",
         "facts": [{"symbol": "right_angle", "role": "concl", "polarity": "pos", "raw": "", "via": None},
                   {"symbol": "onLine", "role": "hyp", "polarity": "pos", "raw": "", "via": "distinctPointsOnLine"}],
         "cited_props": []},
    ]


def _runf(monkeypatch, capsys, argv):
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (_facts_rows(), 0))
    code = F.main(argv)
    return code, capsys.readouterr().out


def test_main_symbol_source_form_aliases(monkeypatch, capsys):
    # Triangle.area is aliased to 'area' → matches the area-concluding axiom
    c1, o1 = _runf(monkeypatch, capsys, ["--concludes", "Triangle.area"])
    assert c1 == 0 and "parallelogram_area" in o1
    # ∟ is aliased to 'right_angle'
    c2, o2 = _runf(monkeypatch, capsys, ["--concludes", "∟"])
    assert c2 == 0 and "proposition_11" in o2
    # both equal their canonical form's result
    _, oc = _runf(monkeypatch, capsys, ["--concludes", "area"])
    assert "parallelogram_area" in oc


def test_main_unknown_symbol_errors_with_suggestion(monkeypatch, capsys):
    code, out = _runf(monkeypatch, capsys, ["--concludes", "bogus"])
    assert code == 2
    assert "unknown symbol 'bogus'" in out
    assert "valid symbols:" in out                              # lists the canonical set


def test_main_unknown_symbol_suggests_close_match(monkeypatch, capsys):
    code, out = _runf(monkeypatch, capsys, ["--concludes", "ono"])   # close to onLine
    assert code == 2 and "did you mean" in out


def test_main_negation_through_alias(monkeypatch, capsys):
    # ¬ prefix + dotted source form together: ¬Line.intersectsLine → (intersectsLine, neg)
    rows = [{"kind": "prop", "name": "p_parallel", "source": "Book/Prop27.lean:6", "signature": "…",
             "docstring": "", "cited_props": [],
             "facts": [{"symbol": "intersectsLine", "role": "concl", "polarity": "neg", "raw": "", "via": None}]}]
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    code = F.main(["--concludes", "¬Line.intersectsLine"])
    out = capsys.readouterr().out
    assert code == 0 and "p_parallel" in out


# ── --grep over signature + docstring ────────────────────────────────────────────────────────────────
def test_main_grep_matches_signature(monkeypatch, capsys):
    rows = [{"kind": "prop", "name": "has_double", "source": "Book2/Prop04/Main.lean:1",
             "signature": "∀ …, x = a + b + 2 * (c)", "docstring": "", "facts": [], "cited_props": []},
            {"kind": "prop", "name": "no_double", "source": "Book/Prop01.lean:1",
             "signature": "∀ …, x = a + b", "docstring": "", "facts": [], "cited_props": []}]
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    code = F.main(["--grep", r"2 \*"])                          # literal doubling in the SIGNATURE
    out = capsys.readouterr().out
    assert code == 0 and "has_double" in out and "no_double" not in out


def test_main_grep_still_matches_docstring(monkeypatch, capsys):
    rows = [{"kind": "helper", "name": "h1", "source": "Helpers/Area.lean:16", "signature": "x = y",
             "docstring": "repackaged from the area axiom", "facts": [], "cited_props": []}]
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    code = F.main(["--grep", "repackaged"])
    out = capsys.readouterr().out
    assert code == 0 and "h1" in out


# ── output projection (--show) + truncation + footer ────────────────────────────────────────────────────
def test_main_default_projection_is_filtered_region(monkeypatch, capsys):
    # --concludes defaults to showing the CONCLUSION region
    _, out = _runf(monkeypatch, capsys, ["--concludes", "area"])
    assert "Triangle.area △ a:c:d" in out                       # conclusion shown
    assert "formParallelogram a b c d" not in out               # hypothesis NOT shown by default


def test_main_show_hyps_independent_of_filter(monkeypatch, capsys):
    # same area query, but --show hyps prints the HYPOTHESIS instead — projection ≠ filter
    _, out = _runf(monkeypatch, capsys, ["--concludes", "area", "--show", "hyps"])
    assert "formParallelogram a b c d" in out
    assert "Triangle.area △ a:c:d" not in out


def test_main_show_conclusion_without_concludes_filter(monkeypatch, capsys):
    # --show works even when you filtered by --name (not --concludes)
    _, out = _runf(monkeypatch, capsys, ["--name", "parallelogram_area", "--show", "conclusion"])
    assert "Triangle.area △ a:c:d" in out
    assert "formParallelogram a b c d" not in out


def test_main_show_full_prints_whole_signature(monkeypatch, capsys):
    _, out = _runf(monkeypatch, capsys, ["--name", "parallelogram_area", "--show", "full"])
    assert "formParallelogram a b c d" in out and "Triangle.area △ a:c:d" in out


def test_main_invalid_show_errors(monkeypatch, capsys):
    code, out = _runf(monkeypatch, capsys, ["--concludes", "area", "--show", "bogus"])
    assert code == 2 and "--show takes one of" in out


def test_main_few_results_never_truncate(monkeypatch, capsys):
    # a SINGLE massive-signature match must NOT be truncated (one row is no wall)
    long_sig = "∀ …, " + "x" * 400
    rows = [{"kind": "prop", "name": "wide", "source": "Book/Prop01.lean:1", "signature": long_sig,
             "docstring": "", "facts": [], "cited_props": []}]
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    F.main(["--name", "wide"])
    out = capsys.readouterr().out
    assert "x" * 400 in out                                     # shown WHOLE, not cut
    assert "truncated" not in out


def test_main_massive_line_truncated_only_in_long_list(monkeypatch, capsys):
    # >5 rows AND one >200-char line → only the massive line is cut (by CHARACTER, not terminal width)
    rows = [{"kind": "prop", "name": f"p{i:02}", "source": f"Book/Prop{i:02}.lean:1",
             "signature": "x = y", "docstring": "", "facts": [], "cited_props": []} for i in range(1, 7)]
    rows.append({"kind": "prop", "name": "big", "source": "Book/Prop99.lean:1",
                 "signature": "∀ …, " + "z" * 400, "docstring": "", "facts": [], "cited_props": []})
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    F.main(["--name", "*"])                                     # default: the big line truncated
    out = capsys.readouterr().out
    assert "…" in out and "truncated" in out
    assert "z" * 400 not in out                                 # the massive one was cut
    assert "x = y" in out                                       # the normal-length ones shown whole
    # --wide → nothing truncated, even the massive line
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    F.main(["--name", "*", "--wide"])
    out2 = capsys.readouterr().out
    assert "z" * 400 in out2                                    # massive line shown whole under --wide
    assert "truncated" not in out2


def test_main_footer_book_breakdown_when_many(monkeypatch, capsys):
    rows = [{"kind": "prop", "name": f"p{i}", "source": f"Book/Prop{i:02}.lean:1",
             "signature": "x", "docstring": "", "facts": [], "cited_props": []} for i in range(1, 9)]
    rows += [{"kind": "prop", "name": f"q{i}", "source": f"Book2/Prop{i:02}/Main.lean:1",
              "signature": "x", "docstring": "", "facts": [], "cited_props": []} for i in range(1, 9)]
    monkeypatch.setattr(F.B, "ensure_fresh", lambda force=False: (rows, 0))
    F.main(["--name", "*"])                                     # 16 matches → breakdown shown
    out = capsys.readouterr().out
    assert "Book1:8" in out and "Book2:8" in out
    assert "narrow with" in out
