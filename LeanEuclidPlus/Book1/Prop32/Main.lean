import SystemE
import Book.Prop31
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_32 : ∀ (a b c d : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (between b c d) →
  ∠ a:c:d = ∠ c:a:b + ∠ a:b:c ∧
  ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ := by
  euclid_intros
  euclid_intro_sentence "1.32.0"
    "In any triangle,  (if) one of the sides (is) produced  (then) the external angle is equal to the (sum of the) two internal and opposite (angles), and the (sum of the) three internal angles of the triangle is equal to two right-angles. Let $ABC$ be a triangle, and let one of its sides $BC$ have been produced to $D$. I say that the external angle $ACD$ is equal to the (sum of the) two internal and opposite angles $CAB$ and $ABC$, and the (sum of the) three internal angles of the triangle---$ABC$, $BCA$, and $CAB$---is equal to two right-angles. "

  euclid_apply (proposition_31 c a b AB) as CE
  euclid_apply (point_on_line_same_side BC CE a) as e
  euclid_sentence "1.32.1"
    "For let $CE$ have been drawn through point $C$ parallel to the straight-line $AB$ [Prop.~1.31]. "
    (step1 : c.onLine CE ∧ e.onLine CE ∧ ¬(CE.intersectsLine AB)) := by sorry

  -- @assumption_valid
  have step2_assumption1 : ¬(AB.intersectsLine CE) := by euclid_finish
  -- @assumption_valid
  have step2_assumption2 : distinctPointsOnLine a c AC := by euclid_finish
  -- @assumption ("$AB$ is parallel to $CE$", ¬(AB.intersectsLine CE))
  -- @assumption ("$AC$ has fallen across them", distinctPointsOnLine a c AC)
  euclid_sentence "1.32.2"
    "And since $AB$ is parallel to $CE$, and $AC$ has fallen across them, the alternate angles $BAC$ and $ACE$ are equal to one another [Prop.~1.29]."
    (step2 : ∠ b:a:c = ∠ a:c:e) := by sorry

  -- @assumption_valid
  have step3_assumption1 : ¬(AB.intersectsLine CE) := by assumption
  -- @assumption_valid
  have step3_assumption2 : distinctPointsOnLine b d BC := by euclid_finish
  -- @assumption ("$AB$ is parallel to $CE$", ¬(AB.intersectsLine CE))
  -- @assumption ("the straight-line $BD$ has fallen across them", distinctPointsOnLine b d BC)
  euclid_sentence "1.32.3"
    "Again, since $AB$ is parallel to $CE$, and the straight-line $BD$ has fallen across them,  the external angle $ECD$ is equal to the internal and opposite (angle) $ABC$ [Prop.~1.29]."
    (step3 : ∠ e:c:d = ∠ a:b:c) := by sorry

  euclid_sentence "1.32.4"
    "But $ACE$ was also shown (to be) equal to $BAC$."
    (step4 : ∠ a:c:e = ∠ b:a:c) := by sorry

  euclid_sentence "1.32.5"
    "Thus, the whole angle $ACD$ is equal to the (sum of the) two internal and opposite (angles) $BAC$ and $ABC$. "
    (step5 : ∠ a:c:d = ∠ b:a:c + ∠ a:b:c) := by sorry

  euclid_sentence "1.32.6"
    "Let $ACB$ have been added to both."
    (step6 : ∠ a:c:d + ∠ a:c:b = ∠ b:a:c + ∠ a:b:c + ∠ a:c:b) := by sorry

  euclid_sentence "1.32.7"
    "Thus, (the sum of) $ACD$ and $ACB$ is equal to the (sum of the) three (angles) $ABC$, $BCA$, and $CAB$."
    (step7 : ∠ a:c:d + ∠ a:c:b = ∠ a:b:c + ∠ b:c:a + ∠ c:a:b) := by sorry

  euclid_sentence "1.32.8"
    "But, (the sum of) $ACD$ and $ACB$ is equal to two right-angles [Prop.~1.13]."
    (step8 : ∠ a:c:d + ∠ a:c:b = ∟ + ∟) := by sorry

  euclid_sentence "1.32.9"
    "Thus, (the sum of) $ACB$, $CBA$, and $CAB$ is also equal to two right-angles. "
    (step9 : ∠ a:c:b + ∠ c:b:a + ∠ c:a:b = ∟ + ∟) := by sorry

  have hgoal1 : ∠ a:c:d = ∠ c:a:b + ∠ a:b:c := by sorry
  have hgoal2 : ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ := by sorry
  exact ⟨hgoal1, hgoal2⟩
  euclid_conclude_sentence "1.32.10"
    "Thus, in any triangle,  (if) one of the sides  (is) produced (then) the external angle is equal to the (sum of the) two internal and opposite (angles), and the (sum of the) three internal angles of the triangle is equal to two right-angles. (Which is) the very thing it was required to show."

end Elements.Book1
