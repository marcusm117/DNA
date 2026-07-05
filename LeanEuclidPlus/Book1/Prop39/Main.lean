import SystemE
import Book.Prop31
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_39 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ a.sameSide d BC ∧
  (△ a:b:c : ℝ) = (△ d:b:c) ∧ distinctPointsOnLine a d AD →
  ¬(AD.intersectsLine BC) := by
  euclid_intros
  euclid_intro_sentence "1.39.0"
    "Equal triangles which are on the same base, and on the same side, are also between the same parallels.  Let $ABC$ and $DBC$ be equal triangles which are on the same base $BC$, and on the same side (of it). I say that they are also between the same parallels. "

  euclid_sentence "1.39.1"
    "For let $AD$ have been joined."
    (step1 : distinctPointsOnLine a d AD) := by sorry

  euclid_wts "1.39.2"
    "I say that $AD$ and $BC$ are parallel. "

  -- Reductio ("For, if not"): euclid_intros already introduced AD.intersectsLine BC; goal is False.
  euclid_apply (proposition_31 a b c BC) as AE
  euclid_sentence "1.39.3"
    "For, if not, let $AE$ have been drawn through point A parallel to the straight-line $BC$ [Prop.~1.31],"
    (step3 : a.onLine AE ∧ ¬(AE.intersectsLine BC)) := by sorry

  euclid_apply (intersection_lines AE BD) as e
  euclid_apply (line_from_points e c) as EC
  euclid_sentence "1.39.4"
    "and let $EC$ have been joined."
    (step4 : distinctPointsOnLine e c EC) := by sorry

  -- @assumption_valid
  have step5_assumption1 : ¬(AE.intersectsLine BC) := by assumption
  -- @assumption ("on the same base as it, $BC$, and between the same parallels", ¬(AE.intersectsLine BC))
  euclid_sentence "1.39.5"
    "Thus, triangle $ABC$ is equal to triangle $EBC$. For it is on the same base as it, $BC$, and between the same parallels [Prop.~1.37]."
    (step5 : Triangle.area △ a:b:c = Triangle.area △ e:b:c) := by sorry

  -- re-invokes the given △ABC = △DBC for the transitivity below
  euclid_sentence "1.39.6"
    "But $ABC$ is equal to $DBC$."
    (step6 : Triangle.area △ a:b:c = Triangle.area △ d:b:c) := by sorry

  euclid_sentence "1.39.7"
    "Thus, $DBC$ is also equal to $EBC$, the greater to the lesser."
    (step7 : Triangle.area △ d:b:c = Triangle.area △ e:b:c) := by sorry

  -- "the very thing" = the equality △DBC = △EBC (step7); it is impossible (they are unequal).
  euclid_sentence "1.39.8"
    "The very thing is impossible."
    (step8 : Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c) := by sorry

  euclid_sentence "1.39.9"
    "Thus, $AE$ is not parallel to $BC$."
    (step9 : AE.intersectsLine BC) := by sorry

  euclid_sentence "1.39.10"
    "Similarly, we can show that neither (is) any other (straight-line) than $AD$."
    (step10 : ∀ (L : Line), a.onLine L → L ≠ AD → L.intersectsLine BC) := by sorry

  euclid_sentence "1.39.11"
    "Thus, $AD$ is parallel to $BC$. "
    (step11 : ¬(AD.intersectsLine BC)) := by sorry

  exact step11 ‹AD.intersectsLine BC›
  euclid_conclude_sentence "1.39.12"
    "Thus, equal triangles which are on the same base, and on the same side, are also between the same parallels. (Which is) the very thing it was required to show."

end Elements.Book1
