# License: Apache 2.0
# noqa: F841
# pylint: disable=unused-variable


# Standard Library Modules
import os

# Internal Modules
from dna.leaneuclid import EquivalenceChecker

CHECKER_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../LeanEuclidPlus"))
OUTPUT_DIR = os.path.abspath(os.path.dirname(__file__))


def run_single_test(checker: EquivalenceChecker, ground: str, pred: str, test_name: str) -> str:
    """Run a single equivalence test with separate premises and conclusions checking."""
    print("*" * 100)
    print(test_name)

    final_result, _, _ = checker.check(ground, pred, test_name)

    print("*" * 100)
    return final_result


def run_all_tests(checker: EquivalenceChecker, test_cases: list[tuple[str, str, str]]) -> None:
    # Run all  tests
    results = []
    for ground, pred, test_name in test_cases:
        result = run_single_test(checker, ground, pred, test_name)
        results.append(result)

    # Print summary
    total_tests = len(results)
    # Number of passed tests is the number of "equiv" results
    passed_tests = sum(1 for res in results if res == "equiv")
    # Number of likely equivalent tests is the number of "likely_equiv" results
    likely_tests = sum(1 for res in results if res == "likely_equiv")
    # Number of incomplete tests with errors is the number of False results
    error_tests = sum(1 for res in results if res == "checking_error")
    # Other cases are considered failed tests
    failed_tests = total_tests - passed_tests - likely_tests - error_tests

    print("=" * 60)
    print("📊 OVERALL TEST SUMMARY")
    print("=" * 60)
    print(f"✅ Passed: {passed_tests}/{total_tests} Tests")
    print(f"🔍 Likely: {likely_tests}/{total_tests} Tests, Need Review!")
    print(f"❌ Failed: {failed_tests}/{total_tests} Tests")
    print(f"⚠️  Errors: {error_tests}/{total_tests} Tests, Need Review!")

    if passed_tests == total_tests:
        print("🎉 All Tests Passed!")

    print("=" * 60)


def main() -> None:
    # TEST 1: redundant premises
    pred_1 = (  # noqa: F841
        "∀ (Q S T R U : Point) (QS QT ST RU : Line), distinctPointsOnLine Q S QS ∧ distinctPointsOnLine Q T QT ∧ "
        "distinctPointsOnLine S T ST ∧ distinctPointsOnLine R U RU ∧ QS.intersectsLine RU ∧ R.onLine QS ∧ "
        "between Q R S ∧ QT.intersectsLine RU ∧ U.onLine QT ∧ between Q U T ∧ ∠ Q:R:U = ∠ Q:U:R ∧ "
        "¬ ST.intersectsLine RU → ∠ R:S:T = ∠ S:T:Q"
    )
    ground_1 = (  # noqa: F841
        "∀ (Q S T R U : Point) (QS QT ST RU : Line), distinctPointsOnLine Q S QS ∧ distinctPointsOnLine Q T QT ∧ "
        "distinctPointsOnLine S T ST ∧ distinctPointsOnLine R U RU ∧ QS.intersectsLine RU ∧ R.onLine QS ∧ "
        "between Q R S ∧ QT.intersectsLine RU ∧ U.onLine QT ∧ between Q U T ∧ QS.intersectsLine ST ∧ "
        "QT.intersectsLine ST ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ ST.intersectsLine RU → ∠ R:S:T = ∠ S:T:Q"
    )

    # TEST 2: different expression for the same angle
    # ∠ X:W:V v.s. ∠ T:W:V
    pred_2 = (  # noqa: F841
        "∀ (T V W U X : Point) (TV TW UX VW : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine T W TW ∧ "
        "distinctPointsOnLine U X UX ∧ distinctPointsOnLine V W VW ∧ TV.intersectsLine UX ∧ U.onLine TV ∧ "
        "between T U V ∧ TW.intersectsLine UX ∧ X.onLine TW ∧ between T X W ∧ TV.intersectsLine VW ∧ "
        "TW.intersectsLine VW ∧ ∠ T:U:X = ∠ X:W:V ∧ ¬ UX.intersectsLine VW → ∠ U:V:W = ∠ X:W:V"
    )
    ground_2 = (  # noqa: F841
        "∀ (T V W U X : Point) (TV TW UX VW : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine T W TW ∧ "
        "distinctPointsOnLine U X UX ∧ distinctPointsOnLine V W VW ∧ TV.intersectsLine UX ∧ U.onLine TV ∧ "
        "between T U V ∧ TW.intersectsLine UX ∧ X.onLine TW ∧ between T X W ∧ TV.intersectsLine VW ∧ "
        "TW.intersectsLine VW ∧ ∠ T:U:X = ∠ T:W:V ∧ ¬ UX.intersectsLine VW → ∠ U:V:W = ∠ T:W:V"
    )

    # TEST 3: different expression for two lines intersecting at a point
    # twoLinesIntersectAtPoint AB CD D v.s. AB.intersectsLine CD ∧ D.onLine AB
    pred_3 = (  # noqa: F841
        "∀ (T V W U X : Point) (TV TW UX VW : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine T W TW ∧ "
        "distinctPointsOnLine U X UX ∧ distinctPointsOnLine V W VW ∧ twoLinesIntersectAtPoint TV UX U ∧ "
        "between T U V ∧ twoLinesIntersectAtPoint TW UX X ∧ between T X W ∧ TV.intersectsLine VW ∧ "
        "TW.intersectsLine VW ∧ ∠ T:U:X = ∠ T:W:V ∧ ¬ UX.intersectsLine VW → ∠ U:V:W = ∠ T:W:V"
    )
    ground_3 = (  # noqa: F841
        "∀ (T V W U X : Point) (TV TW UX VW : Line), distinctPointsOnLine T V TV ∧ distinctPointsOnLine T W TW ∧ "
        "distinctPointsOnLine U X UX ∧ distinctPointsOnLine V W VW ∧ TV.intersectsLine UX ∧ U.onLine TV ∧ "
        "between T U V ∧ TW.intersectsLine UX ∧ X.onLine TW ∧ between T X W ∧ TV.intersectsLine VW ∧ "
        "TW.intersectsLine VW ∧ ∠ T:U:X = ∠ T:W:V ∧ ¬ UX.intersectsLine VW → ∠ U:V:W = ∠ T:W:V"
    )

    # TEST 4: changed redudant premises
    # between W Z X -> between X Z V
    pred_4 = (  # noqa: F841
        "∀ (W X V Y Z : Point) (WX VY VX WY : Line), distinctPointsOnLine W X WX ∧ distinctPointsOnLine V Y VY ∧ "
        "distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ twoLinesIntersectAtPoint VX WY Z ∧ "
        "between W Z X ∧ between W Z Y ∧ (∠ Y:V:Z) = (∠ V:Y:Z) ∧ ¬ WX.intersectsLine VY → (∠ X:W:Z) = (∠ W:X:Z)"
    )
    ground_4 = (  # noqa: F841
        "∀ (W X V Y Z : Point) (WX VY VX WY : Line), distinctPointsOnLine W X WX ∧ distinctPointsOnLine V Y VY ∧ "
        "distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ twoLinesIntersectAtPoint VX WY Z ∧ "
        "between X Z V ∧ between W Z Y ∧ (∠ Y:V:Z) = (∠ V:Y:Z) ∧ ¬ WX.intersectsLine VY → (∠ X:W:Z) = (∠ W:X:Z)"
    )

    # TEST 5: redudant premises
    # between X Z V
    pred_5 = (  # noqa: F841
        "∀ (W X V Y Z : Point) (WX VY VX WY : Line), distinctPointsOnLine W X WX ∧ distinctPointsOnLine V Y VY ∧ "
        "distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ twoLinesIntersectAtPoint VX WY Z ∧ "
        "between X Z V ∧ between W Z Y ∧ (∠ Y:V:Z) = (∠ V:Y:Z) ∧ ¬ WX.intersectsLine VY → (∠ X:W:Z) = (∠ W:X:Z)"
    )
    ground_5 = (  # noqa: F841
        "∀ (W X V Y Z : Point) (WX VY VX WY : Line), distinctPointsOnLine W X WX ∧ distinctPointsOnLine V Y VY ∧ "
        "distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ twoLinesIntersectAtPoint VX WY Z ∧ "
        "between W Z Y ∧ (∠ Y:V:Z) = (∠ V:Y:Z) ∧ ¬ WX.intersectsLine VY → (∠ X:W:Z) = (∠ W:X:Z)"
    )

    # TEST 6: opposing sides (2 lines)
    pred_6 = (  # noqa: F841
        "∀ (S W X Y Z : Point) (WY SZ: Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint WY SZ X ∧ W.opposingSides Y SZ"
    )
    ground_6 = (  # noqa: F841
        "∀ (S W X Y Z : Point) (WY SZ: Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y"
    )

    # TEST 7: opposing sides (3 lines, need to infer W.opposingSides Y SZ)
    pred_7 = (  # noqa: F841
        "∀ (S T U V W X Y Z : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ W.sameSide T SZ ∧ "
        "V.sameSide Y SZ ∧ W.opposingSides V SZ ∧ T.opposingSides Y SZ"
    )
    ground_7 = (  # noqa: F841
        "∀ (S T U V W X Y Z : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ W.sameSide T SZ ∧ "
        "V.sameSide Y SZ ∧ between W X Y ∧ between T U V"
    )

    # TEST 8: opposing sides (model prediction v.s. provided ground truth)
    # just premises, only difference is permutation
    pred_8 = (  # noqa: F841
        "∀ (S T U V W X Y Z : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ W.sameSide T SZ ∧ "
        "V.sameSide Y SZ ∧ W.opposingSides V SZ ∧ T.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟"
    )
    ground_8 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ "
        "between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ "
        "between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟"
    )

    # TEST 9: opposing sides (model prediction v.s. provided ground truth)
    # only differences are permutation &
    # W.opposingSides Y SZ v.s. between W X Y
    pred_9 = (  # noqa: F841
        "∀ (S T U V W X Y Z : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ W.sameSide T SZ ∧ "
        "V.sameSide Y SZ ∧ W.opposingSides V SZ ∧ T.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )
    ground_9 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ "
        "between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ "
        "between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )

    # TEST 10: opposing sides (model prediction v.s. provided ground truth)
    # exact the same expressions except for
    # W.opposingSides Y SZ v.s. between W X Y
    pred_10 = (  # noqa: F841
        "∀ (S T U V W X Y Z : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ W.sameSide T SZ ∧ "
        "V.sameSide Y SZ ∧ W.opposingSides V SZ ∧ T.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )
    ground_10 = (  # noqa: F841
        "∀ (S T U V W X Y Z : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ W.sameSide T SZ ∧ "
        "V.sameSide Y SZ ∧ between W X Y ∧ between T U V ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )

    # TEST 11: opposing sides (2 lines), correct formulas
    premises_t2g_11 = (  # noqa: F841
        "∀ (S W X Y Z : Point) (WY SZ: Line), (distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint WY SZ X ∧ W.opposingSides Y SZ) → "
        "(distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "between W X Y)"
    )
    premises_g2t_11 = (  # noqa: F841
        "∀ (S W X Y Z : Point) (WY SZ: Line), (distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y) → "
        "(distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "W.opposingSides Y SZ)"
    )

    # TEST 12: opposing sides (model prediction v.s. provided ground truth), correct formulas
    premises_t2g_12 = (  # noqa: F841
        "∀ (S T U V W X Y Z : Point) (WY SZ TV : Line), (distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ W.sameSide T SZ ∧ "
        "V.sameSide Y SZ ∧ W.opposingSides V SZ ∧ T.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟) → "
        "(distinctPointsOnLine T V TV ∧ distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "between W X Y ∧ between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟)"
    )
    premises_g2t_12 = (  # noqa: F841
        "∀ (S T U V W X Y Z : Point) (WY SZ TV : Line), (distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ "
        "between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ "
        "between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟) → "
        "(distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ "
        "twoLinesIntersectAtPoint WY SZ X ∧ twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ "
        "between X U S ∧ W.sameSide T SZ ∧ V.sameSide Y SZ ∧ W.opposingSides V SZ ∧ T.opposingSides Y SZ ∧ "
        "∠ W:X:Z + ∠ S:U:T = ∟ + ∟)"
    )

    # TEST 13: redundant premises
    pred_13 = (  # noqa: F841
        "∀ (W Y S Z T V X U : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ (T.sameSide W SZ ∧ T ≠ W) ∧ "
        "(V.sameSide Y SZ ∧ V ≠ Y) ∧ T.opposingSides V SZ ∧ W.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )
    ground_13 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ "
        "T.opposingSides V SZ ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ W.opposingSides Y SZ ∧ "
        "between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )

    # TEST 14: redundant premises
    pred_14 = (  # noqa: F841
        "∀ (W Y S Z T V X U : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ (T.sameSide W SZ ∧ T ≠ W) ∧ "
        "(V.sameSide Y SZ ∧ V ≠ Y) ∧ T.opposingSides V SZ ∧ W.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )
    ground_14 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ "
        "between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ "
        "between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )

    # TEST 15: permutation only
    pred_15 = (  # noqa: F841
        "∀ (W Y S Z T V X U : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ (T.sameSide W SZ ∧ T ≠ W) ∧ "
        "(V.sameSide Y SZ ∧ V ≠ Y) ∧ T.opposingSides V SZ ∧ W.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )
    ground_15 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ "
        "T.opposingSides V SZ ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ W.opposingSides Y SZ ∧ "
        "between U X Z ∧ (T.sameSide W SZ ∧ T ≠ W) ∧ (V.sameSide Y SZ ∧ V ≠ Y) ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )

    # TEST 16: only difference is parentheses
    pred_16 = (  # noqa: F841
        "∀ (W Y S Z T V X U : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ (T.sameSide W SZ ∧ T ≠ W) ∧ "
        "(V.sameSide Y SZ ∧ V ≠ Y) ∧ T.opposingSides V SZ ∧ W.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )
    ground_16 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ "
        "T.opposingSides V SZ ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ W.opposingSides Y SZ ∧ "
        "between U X Z ∧ T.sameSide W SZ ∧ T ≠ W ∧ V.sameSide Y SZ ∧ V ≠ Y ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )

    # TEST 17: only differences are
    # parentheses &
    # W.opposingSides Y SZ v.s. between W X Y &
    # T ≠ W ∧ V ≠ Y
    pred_17 = (  # noqa: F841
        "∀ (W Y S Z T V X U : Point) (WY SZ TV : Line), distinctPointsOnLine W Y WY ∧ "
        "distinctPointsOnLine S Z SZ ∧ distinctPointsOnLine T V TV ∧ twoLinesIntersectAtPoint WY SZ X ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between Z X U ∧ between X U S ∧ (T.sameSide W SZ ∧ T ≠ W) ∧ "
        "(V.sameSide Y SZ ∧ V ≠ Y) ∧ T.opposingSides V SZ ∧ W.opposingSides Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )
    ground_17 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ twoLinesIntersectAtPoint TV SZ U ∧ "
        "between T U V ∧ between S U X ∧ twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ "
        "between U X Z ∧ T.sameSide W SZ ∧ V.sameSide Y SZ ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → "
        "¬ WY.intersectsLine TV"
    )

    # TEST 18: Equivalent Angles
    pred_18 = (  # noqa: F841
        "∀ (S T Q R U : Point) (ST TQ SQ RU : Line), (S ≠ T ∧ T ≠ Q ∧ S ≠ Q) ∧ "
        "distinctPointsOnLine S T ST ∧ distinctPointsOnLine T Q TQ ∧ distinctPointsOnLine S Q SQ ∧ "
        "formTriangle S T Q ST TQ SQ ∧ distinctPointsOnLine R U RU ∧ R.onLine SQ ∧ U.onLine TQ ∧ "
        "twoLinesIntersectAtPoint RU SQ R ∧ twoLinesIntersectAtPoint RU TQ U ∧ "
        "(S ≠ R ∧ S ≠ U ∧ T ≠ R ∧ T ≠ U ∧ Q ≠ R ∧ Q ≠ U) ∧ (∠ Q:R:U = ∠ Q:U:R) ∧ "
        "(¬ ST.intersectsLine RU) → (∠ R:S:T = ∠ S:T:Q)"
    )
    ground_18 = (  # noqa: F841
        "∀ (Q S T R U : Point) (QS QT ST RU : Line), distinctPointsOnLine Q S QS ∧ "
        "distinctPointsOnLine Q T QT ∧ distinctPointsOnLine S T ST ∧ distinctPointsOnLine R U RU ∧ "
        "QS.intersectsLine RU ∧ R.onLine QS ∧ between Q R S ∧ QT.intersectsLine RU ∧ U.onLine QT ∧ "
        "between Q U T ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ ST.intersectsLine RU → ∠ R:S:T = ∠ S:T:U"
    )

    # TEST 19: Equivialent Expression for Triangle
    pred_19 = (  # noqa: F841
        "∀ (P Q R S T : Point) (PR PS QT RS: Line), formTriangle P R S PR PS RS ∧ "
        "distinctPointsOnLine Q T QT ∧ QT.intersectsLine PR ∧ Q.onLine PR ∧ "
        "between P Q R ∧ RS.intersectsLine PR ∧ T.onLine PS ∧ between P T S ∧ ∠ P:T:Q = ∠ P:Q:T ∧ "
        "¬ QT.intersectsLine RS → ∠ P:S:R = ∠ Q:R:S"
    )
    ground_19 = (  # noqa: F841
        "∀ (P Q R S T : Point) (PR PS QT RS: Line), distinctPointsOnLine R S RS ∧ distinctPointsOnLine Q T QT ∧ "
        "distinctPointsOnLine P R PR ∧ distinctPointsOnLine P S PS ∧ QT.intersectsLine PR ∧ Q.onLine PR ∧ "
        "between P Q R ∧ RS.intersectsLine PR ∧ T.onLine PS ∧ between P T S ∧ ∠ P:T:Q = ∠ P:Q:T ∧ "
        "¬ QT.intersectsLine RS → ∠ P:S:R = ∠ Q:R:S"
    )

    # TEST 20: Triangles Formed by Two Intersecting Lines
    pred_20 = (  # noqa: F841
        "∀ (V Z Y W X : Point) (VZ ZY YV WX XZ ZW VX WY VY : Line), formTriangle V Z Y VZ ZY YV ∧ "
        "formTriangle W X Z WX XZ ZW ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ "
        "twoLinesIntersectAtPoint VX WY Z ∧ distinctPointsOnLine V Y VY ∧ distinctPointsOnLine W X WX ∧ "
        "¬ WX.intersectsLine VY ∧ ∠ Y:V:Z = ∠ Z:Y:V → ∠ X:W:Z = ∠ W:X:Z"
    )
    ground_20 = (  # noqa: F841
        "∀ (V Y W X Z : Point) (VY WX WY VX : Line), distinctPointsOnLine V Y VY ∧ distinctPointsOnLine W X WX ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine V X VX ∧ twoLinesIntersectAtPoint WY VX Z ∧ "
        "between W Z Y ∧ between V Z X ∧ ¬ WX.intersectsLine VY ∧ ∠ Y:V:Z = ∠ Z:Y:V → ∠ X:W:Z = ∠ W:X:Z"
    )

    # TEST 21: Contradiction in Test Premises
    # pred_21 should be VALID, since its premises is a contradiction
    pred_21 = (  # noqa: F841
        "∀ (W X Z V Y : Point) (WX XZ ZW VY YZ ZV VX WY : Line), formTriangle W X Z WX XZ ZW ∧ "
        "formTriangle V Y Z VY YZ ZV ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ "
        "twoLinesIntersectAtPoint VX WY Z ∧ W.opposingSides X VY ∧ V.opposingSides Y WX ∧ "
        "∠ Y:V:Z = ∠ V:Y:Z ∧ ¬ WX.intersectsLine VY → ∠ X:W:Z = ∠ W:X:Z"
    )
    ground_21 = (  # noqa: F841
        "∀ (W X V Y Z : Point) (WX VY VX WY : Line), distinctPointsOnLine W X WX ∧ distinctPointsOnLine V Y VY ∧ "
        "distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ twoLinesIntersectAtPoint VX WY Z ∧ "
        "between X Z V ∧ between W Z Y ∧ (∠ Y:V:Z) = (∠ V:Y:Z) ∧ ¬ WX.intersectsLine VY → (∠ X:W:Z) = (∠ W:X:Z)"
    )

    # TEST 22: Contradiction in Test Premises II
    # pred_22 should be VALID, since its negation is a contradiction,
    # which is the premises of pred_21
    pred_22 = (  # noqa: F841
        "∀ (W X Z V Y : Point) (WX XZ ZW VY YZ ZV VX WY : Line), ¬ (formTriangle W X Z WX XZ ZW ∧ "
        "formTriangle V Y Z VY YZ ZV ∧ distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ "
        "twoLinesIntersectAtPoint VX WY Z ∧ W.opposingSides X VY ∧ V.opposingSides Y WX ∧ "
        "∠ Y:V:Z = ∠ V:Y:Z ∧ ¬ WX.intersectsLine VY)"
    )
    ground_22 = (  # noqa: F841
        "∀ (W X V Y Z : Point) (WX VY VX WY : Line), distinctPointsOnLine W X WX ∧ distinctPointsOnLine V Y VY ∧ "
        "distinctPointsOnLine V X VX ∧ distinctPointsOnLine W Y WY ∧ twoLinesIntersectAtPoint VX WY Z ∧ "
        "between X Z V ∧ between W Z Y ∧ (∠ Y:V:Z) = (∠ V:Y:Z) ∧ ¬ WX.intersectsLine VY → (∠ X:W:Z) = (∠ W:X:Z)"
    )

    # TEST 23: Pre-Check
    pred_23_original = (  # noqa: F841
        "∀ (S T Q R U : Point) (ST RU SQ TQ : Line), formTriangle S T Q ST SQ TQ ∧ distinctPointsOnLine S Q SQ ∧ "
        "distinctPointsOnLine T Q TQ ∧ distinctPointsOnLine R U RU ∧ R.onLine SQ ∧ U.onLine TQ ∧ RU.intersectsLine SQ ∧ "
        "RU.intersectsLine TQ ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ ST.intersectsLine RU → ∠ R:S:T = ∠ T:Q:S"
    )
    pred_23_variant_1 = (  # noqa: F841
        "∀ (S T Q R U : Point) (ST RU SQ TQ : Line), formTriangle S T Q ST SQ TQ ∧ "
        "distinctPointsOnLine R U RU ∧ R.onLine SQ ∧ U.onLine TQ ∧ RU.intersectsLine SQ ∧ "
        "RU.intersectsLine TQ ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ ST.intersectsLine RU → ∠ R:S:T = ∠ T:Q:S"
    )
    pred_23_variant_2 = (  # noqa: F841
        "∀ (S T Q R U : Point) (ST RU SQ TQ : Line), formTriangle S T Q ST SQ TQ ∧ distinctPointsOnLine S Q SQ ∧ "
        "distinctPointsOnLine R U RU ∧ R.onLine SQ ∧ U.onLine TQ ∧ RU.intersectsLine SQ ∧ "
        "RU.intersectsLine TQ ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ ST.intersectsLine RU → ∠ R:S:T = ∠ T:Q:S"
    )
    pred_23_variant_3 = (  # noqa: F841
        "∀ (S T Q : Point) (ST SQ TQ : Line), formTriangle S T Q ST SQ TQ ∧ distinctPointsOnLine S Q SQ → ∠ Q:S:T = ∠ T:Q:S"
    )
    pred_23_variant_4 = (  # noqa: F841
        "∀ (S T Q : Point) (ST SQ TQ : Line), formTriangle S T Q ST SQ TQ ∧ distinctPointsOnLine S Q SQ → ∠ Q:S:T = ∠ Q:S:T"
    )
    ground_23 = (  # noqa: F841
        "∀ (Q S T R U : Point) (QS QT ST RU : Line), distinctPointsOnLine Q S QS ∧ distinctPointsOnLine Q T QT ∧ "
        "distinctPointsOnLine S T ST ∧ distinctPointsOnLine R U RU ∧ QS.intersectsLine RU ∧ R.onLine QS ∧ between Q R S ∧ "
        "QT.intersectsLine RU ∧ U.onLine QT ∧ between Q U T ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ ST.intersectsLine RU → ∠ R:S:T = ∠ S:T:Q"
    )

    # TEST 24: Pre-Check Ablated
    pred_24 = (  # noqa: F841
        "∀ (Q S T R U : Point) (QS QT ST RU : Line), distinctPointsOnLine Q S QS ∧ distinctPointsOnLine Q T QT ∧ "
        "distinctPointsOnLine S T ST ∧ distinctPointsOnLine R U RU ∧ QS.intersectsLine RU ∧ R.onLine QS ∧ "
        "QT.intersectsLine RU ∧ U.onLine QT ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ ST.intersectsLine RU → ∠ R:S:T = ∠ S:T:Q"
    )
    ground_24 = (  # noqa: F841
        "∀ (Q S T R U : Point) (QS QT ST RU : Line), distinctPointsOnLine Q S QS ∧ distinctPointsOnLine Q T QT ∧ "
        "distinctPointsOnLine S T ST ∧ distinctPointsOnLine R U RU ∧ QS.intersectsLine RU ∧ R.onLine QS ∧ between Q R S ∧ "
        "QT.intersectsLine RU ∧ U.onLine QT ∧ between Q U T ∧ ∠ Q:R:U = ∠ Q:U:R ∧ ¬ ST.intersectsLine RU → ∠ R:S:T = ∠ S:T:Q"
    )

    # TEST 25: Nuemric Values
    pred_25_original = (  # noqa: F841
        "∀ (U S R Y T X V W : Point) (US RY XV SU : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine R Y RY ∧ "
        "distinctPointsOnLine X V XV ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint US RY T ∧ "
        "twoLinesIntersectAtPoint XV RY W ∧ between Y W T ∧ between W T R ∧ V.opposingSides S RY ∧ X.opposingSides U RY ∧ "
        "(|(V─X)| / |(S─U)|) = 1 → ∠ T:W:X = ∠ S:T:W"
    )
    pred_25_variant_1 = (  # noqa: F841
        "∀ (U S R Y T X V W : Point) (US RY XV SU : Line), distinctPointsOnLine U S US ∧ distinctPointsOnLine R Y RY ∧ "
        "distinctPointsOnLine X V XV ∧ distinctPointsOnLine S U SU ∧ twoLinesIntersectAtPoint US RY T ∧ "
        "twoLinesIntersectAtPoint XV RY W ∧ between Y W T ∧ between W T R ∧ V.opposingSides S RY ∧ X.opposingSides U RY ∧ "
        "|(V─X)| = |(S─U)| → ∠ T:W:X = ∠ S:T:W"
    )
    ground_25 = (  # noqa: F841
        "∀ (S U V X R Y T W : Point) (SU VX RY : Line), distinctPointsOnLine S U SU ∧ distinctPointsOnLine V X VX ∧ "
        "distinctPointsOnLine R Y RY ∧ twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between R T W ∧ "
        "twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between T W Y ∧ U.sameSide X RY ∧ U ≠ X ∧ V.sameSide S RY ∧ "
        "V ≠ S ∧ ¬ VX.intersectsLine SU → ∠ T:W:X = ∠ S:T:W"
    )

    # TEST 26: Alternative Formalization of Quadrilateral
    pred_26 = (  # noqa: F841
        "∀ (R S T U : Point) (RS ST RT TU RU : Line), formQuadrilateral R S U T RS TU RU ST ∧ distinctPointsOnLine R T RT ∧ "
        "|(T─U)| = |(R─S)| ∧ ¬ RS.intersectsLine TU → (△ R:T:U).congruent (△ T:R:S)"
    )
    ground_26 = (  # noqa: F841
        "∀ (R S T U : Point) (RS ST RT TU RU : Line), formTriangle R S T RS ST RT ∧ formTriangle R T U RT TU RU ∧ "
        "S.opposingSides U RT ∧ |(T─U)| = |(R─S)| ∧ ¬ RS.intersectsLine TU → (△ R:T:U).congruent (△ T:R:S)"
    )

    # TEST 27: Test Parallelism
    pred_27 = (  # noqa: F841
        "∀ (U W Q X R T V S : Point) (UW QX RT : Line), distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ "
        "distinctPointsOnLine R T RT ∧ twoLinesIntersectAtPoint UW QX V ∧ twoLinesIntersectAtPoint RT QX S ∧ "
        "between X V S ∧ between V S Q ∧ U.opposingSides R QX ∧ T.opposingSides W QX ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )
    ground_27 = (  # noqa: F841
        "∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ distinctPointsOnLine U W UW ∧ "
        "distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ between Q S V ∧ "
        "twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧ "
        "R.sameSide U QX ∧ R ≠ U ∧ T.sameSide W QX ∧ T ≠ W ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )

    # TEST 28: DSL
    pred_28 = (  # noqa: F841
        "∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ "
        "distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ "
        "twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ sequentiallyAlignedList [Q, S, V, X] ∧ sameSideDistinctList [R, U] QX ∧ "
        "sameSideDistinctList [T, W] QX ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )
    pred_28_simplified = (  # noqa: F841
        "∀ (R T U W Q X S V : Point) (RT UW QX : Line), (R.onLine RT ∧ T.onLine RT ∧ ¬R = T) ∧ (U.onLine UW ∧ W.onLine UW ∧ ¬U = W) ∧ "
        "(Q.onLine QX ∧ X.onLine QX ∧ ¬Q = X) ∧ (RT.intersectsLine QX ∧ S.onLine RT ∧ S.onLine QX ∧ ¬RT = QX) ∧ between R S T ∧ "
        "(UW.intersectsLine QX ∧ V.onLine UW ∧ V.onLine QX ∧ ¬UW = QX) ∧ between U V W ∧ (between Q S V ∧ between S V X) ∧ "
        "(R.sameSide U QX ∧ ¬R = U) ∧ (T.sameSide W QX ∧ ¬T = W) ∧ ∠T:S:V + ∠S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )
    ground_28 = (  # noqa: F841
        "∀ (R T U W Q X S V : Point) (RT UW QX : Line), distinctPointsOnLine R T RT ∧ "
        "distinctPointsOnLine U W UW ∧ distinctPointsOnLine Q X QX ∧ twoLinesIntersectAtPoint RT QX S ∧ between R S T ∧ "
        "between Q S V ∧ twoLinesIntersectAtPoint UW QX V ∧ between U V W ∧ between S V X ∧ R.sameSide U QX ∧ R ≠ U ∧ "
        "T.sameSide W QX ∧ T ≠ W ∧ ∠ T:S:V + ∠ S:V:W = ∟ + ∟ → ¬ UW.intersectsLine RT"
    )

    # TEST 29: Similarity
    pred_29 = (  # noqa: F841
        "∀ (G H J I F : Point) (GH HJ JG IF FJ JI HF GI : Line), "
        "formTriangle G H J GH HJ JG ∧ "
        "formTriangle I F J IF FJ JI ∧ "
        "distinctPointsOnLine H F HF ∧ "
        "distinctPointsOnLine G I GI ∧ "
        "twoLinesIntersectAtPoint GI HF J ∧ "
        "between G J I ∧ "
        "between H J F ∧ "
        "|(G─J)| / |(I─J)| = |(H─J)| / |(F─J)| → "
        "∠ G:H:J = ∠ I:F:J ∧ ∠ H:J:G = ∠ F:J:I ∧ ∠ J:G:H = ∠ J:I:F ∧ "
        "|(G─H)| / |(I─F)| = |(H─J)| / |(F─J)| ∧ "
        "|(H─J)| / |(F─J)| = |(J─G)| / |(J─I)| ∧ "
        "|(J─G)| / |(J─I)| = |(G─H)| / |(I─F)|"
    )
    pred_29_variant_1 = (  # noqa: F841
        "∀ (G H J I F : Point) (GH HJ JG IF FJ JI HF GI : Line), "
        "formTriangle G H J GH HJ JG ∧ "
        "formTriangle I F J IF FJ JI ∧ "
        "distinctPointsOnLine H F HF ∧ "
        "distinctPointsOnLine G I GI ∧ "
        "twoLinesIntersectAtPoint GI HF J ∧ "
        "between G J I ∧ "
        "between H J F ∧ "
        "|(G─J)| / |(I─J)| = |(H─J)| / |(F─J)| → "
        "∠ G:H:J = ∠ I:F:J ∧ ∠ H:J:G = ∠ F:J:I ∧ ∠ J:G:H = ∠ J:I:F ∧ "
        "|(G─H)| / |(I─F)| = |(H─J)| / |(F─J)| ∧ "
        "|(H─J)| / |(F─J)| = |(J─G)| / |(J─I)|"
    )
    pred_29_variant_2 = (  # noqa: F841
        "∀ (G H J I F : Point) (GH HJ JG IF FJ JI HF GI : Line), "
        "formTriangle G H J GH HJ JG ∧ "
        "formTriangle I F J IF FJ JI ∧ "
        "distinctPointsOnLine H F HF ∧ "
        "distinctPointsOnLine G I GI ∧ "
        "twoLinesIntersectAtPoint GI HF J ∧ "
        "between G J I ∧ "
        "between H J F ∧ "
        "|(G─J)| / |(I─J)| = |(H─J)| / |(F─J)| → "
        "∠ G:H:J = ∠ I:F:J ∧ ∠ H:J:G = ∠ F:J:I ∧ "
        "|(G─H)| / |(I─F)| = |(H─J)| / |(F─J)| ∧ "
        "|(H─J)| / |(F─J)| = |(J─G)| / |(J─I)| ∧ "
        "|(J─G)| / |(J─I)| = |(G─H)| / |(I─F)|"
    )
    ground_29 = (  # noqa: F841
        "∀ (G H J I F : Point) (GH HJ JG IF FJ JI HF GI : Line), "
        "formTriangle G H J GH HJ JG ∧ "
        "formTriangle I F J IF FJ JI ∧ "
        "distinctPointsOnLine H F HF ∧ "
        "distinctPointsOnLine G I GI ∧ "
        "twoLinesIntersectAtPoint GI HF J ∧ "
        "between G J I ∧ "
        "between H J F ∧ "
        "|(G─J)| / |(I─J)| = |(H─J)| / |(F─J)| → "
        "(△ G:H:J).similar (△ I:F:J)"
    )

    # TEST 30: Duplicated Premises
    pred_30 = (  # noqa: F841
        "∀ (H I J K : Point) (HI IJ JH HK : Line), formTriangle H I J HI IJ JH ∧ "
        "distinctPointsOnLine H K HK ∧ twoLinesIntersectAtPoint HK IJ K ∧ "
        "between I K J ∧ distinctPointsOnLine H K HK ∧ ∠ I:H:K = ∠ J:H:K ∧ "
        "|(H─I)| = |(H─J)| → ∠ H:K:I = ∠ H:K:J"
    )
    ground_30 = (  # noqa: F841
        "∀ (H I J K : Point) (HI IJ JH HK : Line), formTriangle H I J HI IJ JH ∧ "
        "distinctPointsOnLine H K HK ∧ twoLinesIntersectAtPoint HK IJ K ∧ "
        "between I K J ∧ ∠ I:H:K = ∠ J:H:K ∧ "
        "|(H─I)| = |(H─J)| → ∠ H:K:I = ∠ H:K:J"
    )

    # TEST 31: test new relations parallel, supplementaryAngles,
    # sequentiallyAlignedList, sameSideDistinctList
    pred_31 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ "
        "twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ "
        "sequentiallyAlignedList [Z, X, U, S] ∧ "
        "sameSideDistinctList [T, W] SZ ∧ sameSideDistinctList [V, Y] SZ ∧ "
        "supplementaryAngles (∠ W:X:Z) (∠ S:U:T) → parallel TV WY"
    )
    ground_31 = (  # noqa: F841
        "∀ (T V W Y S Z U X : Point) (TV WY SZ : Line), distinctPointsOnLine T V TV ∧ "
        "distinctPointsOnLine W Y WY ∧ distinctPointsOnLine S Z SZ ∧ "
        "twoLinesIntersectAtPoint TV SZ U ∧ between T U V ∧ between S U X ∧ "
        "twoLinesIntersectAtPoint WY SZ X ∧ between W X Y ∧ between U X Z ∧ "
        "T.sameSide W SZ ∧ T ≠ W ∧ V.sameSide Y SZ ∧ V ≠ Y ∧ ∠ W:X:Z + ∠ S:U:T = ∟ + ∟ → ¬ WY.intersectsLine TV"
    )

    # TEST 32: test new relation perpendicular
    pred_32 = (  # noqa: F841
        "∀ (G H I J : Point) (GJ IJ : Line), "
        "perpendicular GJ IJ G I J → (△ H:I:J).similar (△ H:J:G)"
    )
    pred_32_variant_1 = (  # noqa: F841
        "∀ (G H I J : Point) (GJ IJ : Line), "
        "perpendicularAt GJ IJ J G I → trianglesSimilar H I J H J G"
    )
    ground_32 = (  # noqa: F841
        "∀ (G H I J : Point) "
        "(GJ IJ : Line), "
        "distinctPointsOnLine I J IJ ∧ distinctPointsOnLine J G GJ ∧ "
        # "twoLinesIntersectAtPoint IJ GJ J ∧ "
        "∠ G:J:I = ∟ → (△ H:I:J).similar (△ H:J:G)"
    )

    # TEST 33: test new relation midpoint
    pred_33 = (  # noqa: F841
        "∀ (H I J K : Point) (HI IJ JH HK : Line), formTriangle H I J HI IJ JH ∧ "
        "distinctPointsOnLine H K HK ∧ twoLinesIntersectAtPoint HK IJ K ∧ "
        "|(H─I)| = |(H─J)| ∧ midpoint I K J → ∠ H:K:J = ∠ H:K:I"
    )
    ground_33 = (  # noqa: F841
        "∀ (H I J K : Point) (HI IJ JH HK : Line), formTriangle H I J HI IJ JH ∧ "
        "distinctPointsOnLine H K HK ∧ twoLinesIntersectAtPoint HK IJ K ∧ "
        "between I K J ∧ |(H─I)| = |(H─J)| ∧ |(K─I)| = |(K─J)| → ∠ H:K:J = ∠ H:K:I"
    )

    # TEST 34: test new relation extendedPointCloserToA, extendedPointCloserToB
    pred_34 = (  # noqa: F841
        "∀ (G H I J K : Point) (GH HK GK HJ : Line), formTriangle G H K GH HK GK ∧ "
        "extendedPointCloserToB G H I ∧ distinctPointsOnLine H J HJ ∧ J.sameSide K GH ∧ J ≠ K ∧ "
        "¬ GK.intersectsLine HJ → ∠ H:G:K + ∠ H:K:G + ∠ G:H:K = ∟ + ∟"
    )
    pred_34_variant_1 = (  # noqa: F841
        "∀ (G H I J K : Point) (GH HK GK HJ : Line), formTriangle G H K GH HK GK ∧ "
        "extendedPointCloserToA H G I ∧ distinctPointsOnLine H J HJ ∧ J.sameSide K GH ∧ J ≠ K ∧ "
        "¬ GK.intersectsLine HJ → ∠ H:G:K + ∠ H:K:G + ∠ G:H:K = ∟ + ∟"
    )
    ground_34 = (  # noqa: F841
        "∀ (G H I J K : Point) (GH HK GK HJ : Line), formTriangle G H K GH HK GK ∧ "
        "between G H I ∧ distinctPointsOnLine H J HJ ∧ J.sameSide K GH ∧ J ≠ K ∧ "
        "¬ GK.intersectsLine HJ → ∠ H:G:K + ∠ H:K:G + ∠ G:H:K = ∟ + ∟"
    )

    # TEST 35: test new relation lineBisectsAngle
    pred_35 = (  # noqa: F841
        "∀ (P Q R S : Point) (PQ RS QR PS PR : Line), "
        "formConvexQuadrilateral P Q S R PQ RS PS QR ∧ distinctPointsOnLine P R PR ∧ "
        "lineBisectsAngle Q P S R PR ∧ lineBisectsAngle Q R S P PR → |(R─S)| = |(Q─R)|"
    )
    ground_35 = (  # noqa: F841
        "∀ (P Q R S : Point) (PQ RS QR PS PR : Line), "
        "formConvexQuadrilateral P Q S R PQ RS PS QR ∧ distinctPointsOnLine P R PR ∧ "
        "∠ Q:P:R = ∠ S:P:R ∧ ∠ P:R:Q = ∠ P:R:S → |(R─S)| = |(Q─R)|"
    )

    # TEST 36: test new relation equilateralTriangle
    pred_36 = (  # noqa: F841
        "∀ (P Q R S T : Point) (PQ QR RS ST PT PS SQ : Line), "
        "formTriangle P S T PS ST PT ∧ formTriangle P Q S PQ SQ PS ∧ "
        "formTriangle Q R S QR RS SQ ∧ P.opposingSides R SQ ∧ Q.opposingSides T PS ∧ "
        "∠ R:Q:S = ∠ S:P:T ∧ |(P─T)| = |(Q─R)| ∧ equilateralTriangle P Q S "
        "→ (△ P:S:T).congruent (△ Q:S:R)"
    )
    ground_36 = (  # noqa: F841
        "∀ (P Q R S T : Point) (PQ QR RS ST PT PS SQ : Line), "
        "formTriangle P S T PS ST PT ∧ formTriangle P Q S PQ SQ PS ∧ "
        "formTriangle Q R S QR RS SQ ∧ P.opposingSides R SQ ∧ Q.opposingSides T PS ∧ "
        "∠ R:Q:S = ∠ S:P:T ∧ |(P─T)| = |(Q─R)| ∧ |(P─Q)| = |(Q─S)| ∧ |(Q─S)| = |(S─P)| "
        "→ (△ P:S:T).congruent (△ Q:S:R)"
    )

    # TEST 37: Circle Naming
    pred_37 = (  # noqa: F841
        "∀ (P Q R S A B : Point) (a b : Circle) (PQ AS BR : Line), P.isCentre a ∧ Q.isCentre b ∧ distinctPointsOnLine P Q PQ ∧ PQ.intersectsCircle a ∧ R.onLine PQ ∧ R.onCircle a ∧ PQ.intersectsCircle b ∧ S.onLine PQ ∧ S.onCircle b ∧ a.intersectsCircle b ∧ A.onCircle a ∧ A.onCircle b ∧ B.onCircle a ∧ B.onCircle b ∧ A.opposingSides B PQ ∧ distinctPointsOnLine A S AS ∧ distinctPointsOnLine B R BR ∧ ¬ AS.intersectsLine BR ∧ ∠ Q:A:S = ∠ P:B:R → (△ Q:S:A).similar (△ R:P:B)"
    )
    ground_37 = (  # noqa: F841
        "∀ (P Q R S A B : Point) (a b : Circle) (PQ AS BR : Line), P.isCentre a ∧ Q.isCentre b ∧ distinctPointsOnLine P Q PQ ∧ PQ.intersectsCircle a ∧ R.onLine PQ ∧ R.onCircle a ∧ PQ.intersectsCircle b ∧ S.onLine PQ ∧ S.onCircle b ∧ a.intersectsCircle b ∧ A.onCircle a ∧ A.onCircle b ∧ B.onCircle a ∧ B.onCircle b ∧ A.opposingSides B PQ ∧ distinctPointsOnLine A S AS ∧ distinctPointsOnLine B R BR ∧ ¬ AS.intersectsLine BR ∧ ∠ Q:A:S = ∠ P:B:R → (△ Q:S:A).similar (△ R:P:B)"
    )

    # BINARY TESTS
    # binary_checker = EquivalenceChecker(  # noqa: F841
    #     root_dir=CHECKER_DIR,
    #     mode="skipApprox",
    #     bin_time=30,
    #     tmp_dir=os.path.join(OUTPUT_DIR, os.path.dirname(__file__), "checker_tests", "binary", "lean"),
    #     result_dir=os.path.join(OUTPUT_DIR, os.path.dirname(__file__), "checker_tests", "binary", "result"),
    #     relations_file="Relations",
    # )

    # Define test cases
    binary_test_cases = [  # noqa: F841
        # (ground_1, pred_1, "TEST-1_Redundant-Premises_UniGeo-Parallel-13"),
        # (ground_2, pred_2, "TEST-2_Same-Angle_UniGeo-Parallel-16"),
        # (ground_3, pred_3, "TEST-3_Intersecting-Lines_UniGeo-Parallel-16"),
        # (ground_4, pred_4, "TEST-4_Changed-Redundant-Premises_UniGeo-Parallel-20"),
        # (ground_5, pred_5, "TEST-5_Redundant-Premises_UniGeo-Parallel-20"),
        # (ground_6, pred_6, "TEST-6_Opposing-Sides_UniGeo-Parallel-1_two-lines"),
        # (ground_7, pred_7, "TEST-7_Opposing-Sides_UniGeo-Parallel-1_three-lines"),
        # (ground_8, pred_8, "TEST-8_Opposing-Sides_UniGeo-Parallel-1_premises-perm"),
        # (ground_9, pred_9, "TEST-9_Opposing-Sides_UniGeo-Parallel-1"),
        # (ground_10, pred_10, "TEST-10_Opposing-Sides_UniGeo-Parallel-1_no-perm"),
        # (premises_g2t_11, premises_t2g_11, "TEST-11_Opposing-Sides_UniGeo-Parallel-1_two-lines_correct-formulas"),
        # (premises_g2t_12, premises_t2g_12, "TEST-12_Opposing-Sides_UniGeo-Parallel-1_correct-formulas"),
        (ground_19, pred_19, "TEST-19_Equivalent-Expression-for-Triangle_UniGeo-Parallel-3"),
    ]

    # Run all binary tests
    # run_all_tests(binary_checker, binary_test_cases)

    # SEPARATE TESTS
    # separate_checker = EquivalenceChecker(  # noqa: F841
    #     root_dir=CHECKER_DIR,
    #     mode="separate",
    #     bin_time=15,
    #     tmp_dir=os.path.join(OUTPUT_DIR, os.path.dirname(__file__), "checker_tests", "separate", "lean"),
    #     result_dir=os.path.join(OUTPUT_DIR, os.path.dirname(__file__), "checker_tests", "separate", "result"),
    #     relations_file="Relations",
    # )

    # Define separate test cases
    separate_test_cases = [  # noqa: F841
        # (ground_9, pred_9, "TEST-9_Opposing-Sides_UniGeo-Parallel-1"),
        # (ground_13, pred_13, "TEST-13_Opposing-Sides_UniGeo-Parallel-1"),
        # (ground_14, pred_14, "TEST-14_Opposing-Sides_UniGeo-Parallel-1"),
        # (ground_15, pred_15, "TEST-15_Opposing-Sides_UniGeo-Parallel-1_permutation-only"),
        # (ground_16, pred_16, "TEST-16_Opposing-Sides_UniGeo-Parallel-1_parentheses-only"),
        # (ground_17, pred_17, "TEST-17_Opposing-Sides_UniGeo-Parallel-1_parentheses-and-permutation"),
        # (ground_18, pred_18, "TEST-18_Equivalent-Angles_UniGeo-Parallel-13_equivalent-angles"),
        (ground_19, pred_19, "TEST-19_Equivalent-Expression-for-Triangle_UniGeo-Parallel-3"),
    ]

    # Run all separate tests
    # run_all_tests(separate_checker, separate_test_cases)

    # PRECHECK+SEPARATE TESTS
    precheck_plus_separate_checker = EquivalenceChecker(
        root_dir=CHECKER_DIR,
        mode="precheck+separate",
        bin_time=15,
        tmp_dir=os.path.join(OUTPUT_DIR, "checker_tests", "precheck_plus_separate", "lean"),
        result_dir=os.path.join(OUTPUT_DIR, "checker_tests", "precheck_plus_separate", "result"),
        ground_relations_file="Relations",
        test_relations_file="Relations_oracle",
    )

    # Define separate test cases
    precheck_plus_separate_test_cases = [
        # (ground_9, pred_9, "TEST-9_Opposing-Sides_UniGeo-Parallel-1"),
        # (ground_15, pred_15, "TEST-15_Opposing-Sides_UniGeo-Parallel-1_permutation-only"),
        # (ground_16, pred_16, "TEST-16_Opposing-Sides_UniGeo-Parallel-1_parentheses-only"),
        # (ground_17, pred_17, "TEST-17_Opposing-Sides_UniGeo-Parallel-1_parentheses-and-permutation"),
        # (ground_18, pred_18, "TEST-18_Equivalent-Angles_UniGeo-Parallel-13_equivalent-angles"),
        # (ground_19, pred_19, "TEST-19_Equivalent-Expression-for-Triangle_UniGeo-Parallel-3"),
        # (ground_20, pred_20, "TEST-20_Triangles-Formed-by-Two-Intersecting-Lines_UniGeo-Parallel-10"),
        # (ground_21, pred_21, "TEST-21_Contradiction-in-Test-Premises_UniGeo-Parallel-20"),
        # (ground_23, pred_23_variant_4, "TEST-23_Pre-Check_UniGeo-Parallel-13"),
        # (ground_24, pred_24, "TEST-24_Pre-Check-Ablated_UniGeo-Parallel-13"),
        # (ground_25, pred_25_original, "TEST-25_Numeric-Values_UniGeo-Parallel-7"),
        # (ground_26, pred_26, "TEST-26_Alternative-Formalization-of-Quadrilateral_UniGeo-Congruent-1"),
        # (ground_27, pred_27, "TEST-27_Test-Parallelism_UniGeo-Parallel-3"),
        # (ground_28, pred_28, "TEST-28_DSL_UniGeo-Parallel-3"),
        # (ground_29, pred_29, "TEST-29_Similarity_UniGeo-Parallel-3"),
        # (ground_30, pred_30, "TEST-30_Duplicated-Premises_UniGeo-Triangle-3"),
        # (ground_31, pred_31, "TEST-31_Parallel_UniGeo-Parallel-1"),
        # (ground_32, pred_32_variant_1, "TEST-32_Perpendicular_UniGeo-Similarity-17"),
        # (ground_33, pred_33, "TEST-33_Midpoint_UniGeo-Triangle-1"),
        # (ground_34, pred_34, "TEST-34_Extended-Point-Closer-to-A_UniGeo-Triangle-6"),
        # (ground_34, pred_34_variant_1, "TEST-34_Extended-Point-Closer-to-A_UniGeo-Triangle-6"),
        # (ground_35, pred_35, "TEST-35_Line-Bisects-Angle_UniGeo-Quadrilateral-17"),
        # (ground_36, pred_36, "TEST-36_Equilateral-Triangle_UniGeo-Congruent-8"),
        (ground_37, pred_37, "TEST-37_Circle-Naming_UniGeo-Additional-9"),
    ]

    # Run all separate tests
    run_all_tests(precheck_plus_separate_checker, precheck_plus_separate_test_cases)


if __name__ == "__main__":
    main()
