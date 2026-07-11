import SystemE
import Book3.Prop01.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_21 : ∀ (a b d e : Point) (BD : Line) (ABCD : Circle),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ d.onCircle ABCD ∧ e.onCircle ABCD ∧
  distinctPointsOnLine b d BD ∧
  a.sameSide e BD →
  ∠ b:a:d = ∠ b:e:d :=
by
  euclid_intros
  euclid_intro_sentence "3.21.0"
    "In a circle, angles in the same segment are equal to one another. Let $ABCD$ be a circle, and let $BAD$ and $BED$ be angles in the same segment $BAED$. I say that angles $BAD$ and $BED$ are equal to one another."

  euclid_apply (proposition_1 ABCD) as f'
  euclid_sentence "3.21.1"
    "For let the center of circle $ABCD$ be found [Prop.~3.1], and let it be (at point) $F$."
    (step1 : f'.isCentre ABCD) := by sorry

  euclid_apply (line_from_points b f') as BF
  euclid_apply (line_from_points f' d) as FD
  euclid_sentence "3.21.2"
    "And let $BF$ and $FD$ be joined."
    (step2 : distinctPointsOnLine b f' BF ∧ distinctPointsOnLine f' d FD) := by sorry

  -- @assumption_valid
  have step3_assumption1 : f'.isCentre ABCD := by assumption
  -- @assumption_valid
  have step3_assumption2 : a.onCircle ABCD := by assumption
  -- @assumption_valid
  have step3_assumption3 : b.onCircle ABCD ∧ d.onCircle ABCD ∧ distinctPointsOnLine b d BD := by euclid_finish
  -- @assumption ("angle $BFD$ is at the center", f'.isCentre ABCD)
  -- @assumption ("$BAD$ at the circumference", a.onCircle ABCD)
  -- @assumption ("they have the same circumference base $BCD$", b.onCircle ABCD ∧ d.onCircle ABCD ∧ distinctPointsOnLine b d BD)
  euclid_sentence "3.21.3"
    "And since angle $BFD$ is at the center, and $BAD$ at the circumference, and they have the same circumference base $BCD$, angle $BFD$ is thus double $BAD$ [Prop.~3.20]."
    (step3 : ∠ b:f':d = ∠ b:a:d + ∠ b:a:d) := by sorry

  euclid_sentence "3.21.4"
    "So, for the same (reasons), $BFD$ is also double $BED$."
    (step4 : ∠ b:f':d = ∠ b:e:d + ∠ b:e:d) := by sorry

  euclid_sentence "3.21.5"
    "Thus, $BAD$ (is) equal to $BED$."
    (step5 : ∠ b:a:d = ∠ b:e:d) := by sorry

  exact step5
  euclid_conclude_sentence "3.21.6"
    "Thus, in a circle, angles in the same segment are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book3
