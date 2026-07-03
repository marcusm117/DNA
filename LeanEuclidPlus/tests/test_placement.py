"""Unit tests for the intro/conclude structural-placement gate (faithful_lib.intro_conclude_placement_problems).

`euclid_intro_sentence` / `euclid_conclude_sentence` are STRUCTURAL (no claim) and must bracket the proof:
intro before the first `euclid_sentence`, conclude after the last. A mid-body intro/conclude is a
faithfulness dodge (the Prop10 bug: an "I say that …" demoted to a claimless narrative line mid-proof to
slip past the no-`True` gate). This regression pins that the gate fires."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))

import faithful_lib as L


def _ann(kind, loc, start):
    return {"kind": kind, "loc": loc, "start": start, "ref": f"f.lean:{start}"}


def test_well_bracketed_map_has_no_problems():
    """intro at the front, sentences in the middle, conclude at the end → clean."""
    anns = [
        _ann("intro_sentence", "1.10.0", 0),
        _ann("sentence", "1.10.1", 10),
        _ann("sentence", "1.10.2", 20),
        _ann("conclude_sentence", "1.10.7", 30),
    ]
    assert L.intro_conclude_placement_problems(anns) == []


def test_mid_body_intro_is_flagged():
    """THE Prop10 bug: an intro_sentence AFTER a euclid_sentence is a hard problem."""
    anns = [
        _ann("intro_sentence", "1.10.0", 0),
        _ann("sentence", "1.10.1", 10),
        _ann("sentence", "1.10.2", 20),
        _ann("intro_sentence", "1.10.3", 25),   # "I say that …" demoted, mid-body
        _ann("sentence", "1.10.4", 30),
        _ann("conclude_sentence", "1.10.7", 40),
    ]
    problems = L.intro_conclude_placement_problems(anns)
    assert len(problems) == 1
    assert "1.10.3" in problems[0]
    assert "euclid_intro_sentence" in problems[0] and "mid-proof" in problems[0]


def test_early_conclude_is_flagged():
    """A conclude_sentence BEFORE the last euclid_sentence is a hard problem."""
    anns = [
        _ann("intro_sentence", "1.10.0", 0),
        _ann("sentence", "1.10.1", 10),
        _ann("conclude_sentence", "1.10.7", 20),   # conclude too early
        _ann("sentence", "1.10.2", 30),
    ]
    problems = L.intro_conclude_placement_problems(anns)
    assert len(problems) == 1
    assert "1.10.7" in problems[0]
    assert "euclid_conclude_sentence" in problems[0]


def test_multiple_leading_intros_and_trailing_concludes_ok():
    """More than one intro (split enunciation) is fine as long as all precede the first sentence;
    likewise multiple trailing concludes."""
    anns = [
        _ann("intro_sentence", "2.1.0", 0),
        _ann("intro_sentence", "2.1.1", 5),
        _ann("sentence", "2.1.2", 10),
        _ann("conclude_sentence", "2.1.3", 20),
        _ann("conclude_sentence", "2.1.4", 25),
    ]
    assert L.intro_conclude_placement_problems(anns) == []


def test_no_euclid_sentence_means_no_constraint():
    """Degenerate: with no euclid_sentence there is nothing to bracket → no problems."""
    anns = [
        _ann("intro_sentence", "1.1.0", 0),
        _ann("conclude_sentence", "1.1.1", 10),
    ]
    assert L.intro_conclude_placement_problems(anns) == []


def test_both_violations_reported_together():
    anns = [
        _ann("sentence", "1.1.0", 0),
        _ann("conclude_sentence", "1.1.1", 5),     # before the last sentence
        _ann("sentence", "1.1.2", 10),
        _ann("intro_sentence", "1.1.3", 15),       # after the first sentence
    ]
    problems = L.intro_conclude_placement_problems(anns)
    assert len(problems) == 2
