"""Abbrev unfolding — a positive abbrev emits BOTH the packaged fact and its unfolded atoms (via-tagged);
a negated abbrev emits only the packaged fact (no De Morgan)."""
import os
import re

import faithful_lib as L


def test_formParallelogram_packaged_and_unfolded():
    facts = L.extract_facts("formParallelogram a b c d AB CD AC BD", "hyp")
    # packaged
    pkg = [f for f in facts if f["symbol"] == "formParallelogram"]
    assert len(pkg) == 1 and pkg[0]["via"] is None and pkg[0]["polarity"] == "pos"
    # unfolded atoms carry via=formParallelogram
    unfolded = {(f["symbol"], f["polarity"]) for f in facts if f["via"] == "formParallelogram"}
    assert ("onLine", "pos") in unfolded
    assert ("sameSide", "pos") in unfolded
    assert ("intersectsLine", "neg") in unfolded
    assert ("ne", "neg") in unfolded


def test_distinctPointsOnLine_unfolds_to_onLine_and_ne():
    facts = L.extract_facts("distinctPointsOnLine a b AB", "hyp")
    assert any(f["symbol"] == "distinctPointsOnLine" and f["via"] is None for f in facts)
    vias = {(f["symbol"], f["polarity"]) for f in facts if f["via"] == "distinctPointsOnLine"}
    assert ("onLine", "pos") in vias
    assert ("ne", "neg") in vias


def test_negated_abbrev_packaged_only():
    facts = L.extract_facts("¬(formTriangle a b c AB BC CA)", "hyp")
    pkg = [f for f in facts if f["symbol"] == "formTriangle"]
    assert len(pkg) == 1 and pkg[0]["polarity"] == "neg"
    # no unfolded atoms for a negated abbrev (De Morgan intentionally not attempted)
    assert not any(f["via"] == "formTriangle" for f in facts)


def test_unfold_registry_matches_relations_source():
    """Guard against the hand-transcribed ABBREV_UNFOLD drifting from Relations.lean: the abbrev names
    we unfold must all still be declared as abbrevs in the real Relations.lean."""
    rel = open(os.path.join(L.BOOK_ROOT, "SystemE/Theory/Relations.lean"), encoding="utf-8").read()
    for ab in L.ABBREV_UNFOLD:
        assert re.search(r"\babbrev\s+" + ab + r"\b", rel), f"{ab} no longer an abbrev in Relations.lean"
