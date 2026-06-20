"""SM smell step (check_step --smell) — the PURE, fast pieces: the verdict classifier, the transient
solver-cap swap, and the 'smell' body state. No Lean / no live SMT (matching the repo; check_step has
no automated build tests — the end-to-end is a documented manual smoke)."""
import faithful_lib as L
import check_step as C


# ── classify_smell: the load-bearing build-output → verdict logic ────────────────────────────────────
# The strings below are the EXACT ones euclid_finish / faithful_lib emit (per Solve.lean + lake_build).
def test_classify_closes_on_green_no_sorry():
    assert C.classify_smell(True, "Build completed successfully.") == "closes"


def test_classify_not_closes_when_sorry_present():
    # a green build that still has a sorry is NOT closed
    out = "warning: declaration uses 'sorry'\nBuild completed successfully."
    assert C.classify_smell(True, out) != "closes"


def test_classify_sat_is_false_claim():
    out = "warning: Prover returned SAT\nerror: ..."
    assert C.classify_smell(False, out) == "sat"


def test_classify_hard_on_could_not_prove():
    out = "error: Could not prove: ⊢ ∠ a:b:c = ∟"
    assert C.classify_smell(False, out) == "hard"


def test_classify_wall_on_wall_timeout():
    # faithful_lib's wall-kill message
    out = "[faithful_lib] build of Book2.Prop05.step6 exceeded 20s wall clock — TOO BIG."
    assert C.classify_smell(False, out) == "wall"


def test_classify_error_on_generic_failure():
    out = "error: unknown identifier 'foo'"
    assert C.classify_smell(False, out) == "error"


def test_classify_sat_takes_precedence_over_could_not_prove():
    # if both strings appear, SAT (claim false) is the stronger signal
    out = "warning: Prover returned SAT\nerror: Could not prove: ⊢ ..."
    assert C.classify_smell(False, out) == "sat"


# ── set_solver_cap: transient short cap, distinct from the persisted 30s CAP_LINE ────────────────────
_THM = "import SystemE\n\nnamespace Elements.Book2\n\ntheorem helper_2_1_step1 (b : Point) : True := by\n  trivial\n\nend Elements.Book2\n"


def test_set_solver_cap_injects_when_absent():
    out = L.set_solver_cap(_THM, 5)
    assert "set_option systemE.solverTime 5 in" in out
    assert out.index("solverTime 5") < out.index("theorem")     # above the theorem
    assert "solverTime 30" not in out                           # NOT the canonical 30s cap


def test_set_solver_cap_replaces_existing():
    capped = L.CAP_LINE + "\n" + _THM                           # already has the 30s cap
    out = L.set_solver_cap(capped, 5)
    assert "set_option systemE.solverTime 5 in" in out
    assert "solverTime 30" not in out                           # the 30s line was replaced, not duplicated
    assert out.count("solverTime") == 1


def test_set_solver_cap_idempotent_value():
    once = L.set_solver_cap(_THM, 5)
    twice = L.set_solver_cap(once, 5)
    assert once == twice
    assert twice.count("solverTime") == 1


def test_set_solver_cap_raises_without_theorem():
    import pytest
    with pytest.raises(L.FaithfulError):
        L.set_solver_cap("import SystemE\n-- no theorem here\n", 5)


# ── the 'smell' body state: bare euclid_finish, distinct from wired ──────────────────────────────────
def test_smell_body_regex_matches_bare_euclid_finish():
    # find_body recognizes `:= by euclid_finish` as the 'smell' state
    src = "  have foo : True := by euclid_finish\n"
    sep = src.index(":=")
    state, _s, _e = L.find_body(src, sep, 2, 1, "foo")
    assert state == "smell"


def test_sorry_body_still_matches_sorry_not_smell():
    src = "  have foo : True := by sorry\n"
    sep = src.index(":=")
    state, _s, _e = L.find_body(src, sep, 2, 1, "foo")
    assert state == "sorry"


def test_wired_body_not_misread_as_smell():
    # a WIRED body (euclid_apply (helper…) … ; euclid_finish) must classify as 'wired', NOT 'smell',
    # even though it ends in euclid_finish — the smell shape is a BARE euclid_finish only.
    src = "  have step1 : True := by euclid_apply (helper_2_1_step1 b (by assumption)); euclid_finish\n"
    sep = src.index(":=")
    state, _s, _e = L.find_body(src, sep, 2, 1, "step1")
    assert state == "wired"


# ── _annotate_sat side-win: SAT verdict in ANY output is glossed ─────────────────────────────────────
def test_annotate_sat_glosses_when_present():
    note = C._annotate_sat("warning: Prover returned SAT\n")
    assert "claim is FALSE" in note


def test_annotate_sat_noop_when_absent():
    assert C._annotate_sat("error: Could not prove: ⊢ ...") == ""


def test_fail_output_appends_sat_note():
    out = "error: something\nwarning: Prover returned SAT"
    assert "claim is FALSE" in C._fail_output(out)
