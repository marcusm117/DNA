import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_34 : ∀ (a b c d : Point) (AB CD AC BD BC : Line),
  formParallelogram a b c d AB CD AC BD ∧ distinctPointsOnLine b c BC →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c  = ∠ c:d:b ∧
  Triangle.area △ a:b:c = Triangle.area △ d:c:b := by
  euclid_intros
  euclid_intro_sentence "1.34.0"
    "In parallelogrammic figures the opposite sides and angles are equal to one another, and a diagonal cuts them in half.  Let $ACDB$ be a parallelogrammic figure, and $BC$ its diagonal. I say that for parallelogram $ACDB$, the opposite sides and angles are equal to one another, and the diagonal $BC$ cuts it in half. "

  -- @assumption_valid
  have step1_assumption1 : ¬(AB.intersectsLine CD) := by assumption
  -- @assumption_valid
  have step1_assumption2 : b.onLine AB ∧ b.onLine BC ∧ c.onLine CD ∧ c.onLine BC := by euclid_finish
  -- @assumption ("$AB$ is parallel to $CD$", ¬(AB.intersectsLine CD))
  -- @assumption ("the straight-line $BC$ has fallen across  them", b.onLine AB ∧ b.onLine BC ∧ c.onLine CD ∧ c.onLine BC)
  euclid_sentence "1.34.1"
    "For since $AB$ is parallel to $CD$, and the straight-line $BC$ has fallen across  them, the alternate angles $ABC$ and $BCD$ are equal to one another [Prop.~1.29]. "
    (step1 : ∠ a:b:c = ∠ b:c:d) := by sorry

  -- @assumption_valid
  have step2_assumption1 : ¬(AC.intersectsLine BD) := by assumption
  -- @assumption_valid
  have step2_assumption2 : c.onLine AC ∧ c.onLine BC ∧ b.onLine BD ∧ b.onLine BC := by euclid_finish
  -- @assumption ("$AC$ is parallel to $BD$", ¬(AC.intersectsLine BD))
  -- @assumption ("$BC$ has fallen across them", c.onLine AC ∧ c.onLine BC ∧ b.onLine BD ∧ b.onLine BC)
  euclid_sentence "1.34.2"
    "Again, since $AC$ is parallel to $BD$, and $BC$ has fallen across them, the alternate angles $ACB$ and $CBD$ are equal to one another [Prop.~1.29]. "
    (step2 : ∠ a:c:b = ∠ c:b:d) := by sorry

  -- @assumption_valid
  have step3_assumption1 : ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:a = ∠ c:b:d := by euclid_finish
  -- @assumption ("the two angles $ABC$ and $BCA$ equal to the two (angles) $BCD$ and $CBD$, respectively", ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:a = ∠ c:b:d)
  euclid_sentence "1.34.3"
    "So $ABC$ and $BCD$ are two triangles having the two angles $ABC$ and $BCA$ equal to the two (angles) $BCD$ and $CBD$, respectively, and one side equal to one side---the (one) by the equal angles and common to them, (namely) $BC$."
    (step3 : formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD) := by sorry

  euclid_sentence "1.34.4"
    "Thus, they will also  have the remaining sides  equal to the corresponding remaining (sides), and the remaining angle (equal) to the remaining angle [Prop.~1.26]."
    (step4 : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b) := by sorry

  euclid_sentence "1.34.5"
    "Thus, side $AB$ is equal to $CD$,"
    (step5 : |(a─b)| = |(c─d)|) := by sorry

  euclid_sentence "1.34.6"
    "and $AC$ to $BD$."
    (step6 : |(a─c)| = |(b─d)|) := by sorry

  euclid_sentence "1.34.7"
    "Furthermore, angle $BAC$ is  equal to $CDB$."
    (step7 : ∠ b:a:c = ∠ c:d:b) := by sorry

  -- @assumption_valid
  have step8_assumption1 : ∠ a:b:c = ∠ b:c:d := by assumption
  -- @assumption_valid
  have step8_assumption2 : ∠ c:b:d = ∠ a:c:b := by linarith
  -- @assumption ("angle $ABC$ is equal to $BCD$", ∠ a:b:c = ∠ b:c:d)
  -- @assumption ("$CBD$ to $ACB$", ∠ c:b:d = ∠ a:c:b)
  euclid_sentence "1.34.8"
    "And since angle $ABC$ is equal to $BCD$, and $CBD$ to $ACB$, the whole (angle) $ABD$ is thus equal to the whole (angle) $ACD$."
    (step8 : ∠ a:b:d = ∠ a:c:d) := by sorry

  euclid_sentence "1.34.9"
    "And  $BAC$ was also shown  (to be) equal to $CDB$. "
    (step9 : ∠ b:a:c = ∠ c:d:b) := by sorry

  euclid_sentence "1.34.10"
    "Thus, in parallelogrammic figures the opposite sides and angles are equal to one another. "
    (step10 : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b) := by sorry

  euclid_wts "1.34.11"
    "And, I also say that a diagonal cuts them in half."

  -- @assumption ("$AB$ is equal to $CD$", |(a─b)| = |(c─d)|)
  -- @assumption ("$BC$ (is) common", distinctPointsOnLine b c BC)
  -- BC=CB is the common side of the SAS pairing; kept as its own conjunct per the sentence
  euclid_sentence "1.34.12"
    "For since $AB$ is equal to $CD$, and $BC$ (is) common, the two (straight-lines) $AB$, $BC$ are equal to the two (straight-lines) $DC$, $CB$, respectively."
    (step12 : |(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|) := by sorry

  euclid_sentence "1.34.13"
    "And angle $ABC$ is equal to angle $BCD$."
    (step13 : ∠ a:b:c = ∠ b:c:d) := by sorry

  euclid_sentence "1.34.14"
    "Thus, the base $AC$ (is) also equal to $DB$,"
    (step14 : |(a─c)| = |(d─b)|) := by sorry

  euclid_sentence "1.34.15"
    "and triangle $ABC$ is equal to triangle $BCD$ [Prop.~1.4]. "
    (step15 : Triangle.area △ a:b:c = Triangle.area △ b:c:d) := by sorry

  euclid_sentence "1.34.16"
    "Thus, the diagonal $BC$ cuts the parallelogram $ACDB$ in half."
    (step16 : Triangle.area △ a:b:c = Triangle.area △ d:c:b) := by sorry

  exact ⟨step5, step6, step8, step7, step16⟩
  euclid_conclude_sentence "1.34.17"
    "(Which is) the very thing it was required to show."

end Elements.Book1
