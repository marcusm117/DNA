import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop34.step1
import Book1.Prop34.step2
import Book1.Prop34.step3
import Book1.Prop34.step4
import Book1.Prop34.step5
import Book1.Prop34.step6
import Book1.Prop34.step7
import Book1.Prop34.step8
import Book1.Prop34.step9
import Book1.Prop34.step10
import Book1.Prop34.step12
import Book1.Prop34.step13
import Book1.Prop34.step14
import Book1.Prop34.step15
import Book1.Prop34.step16
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

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
    (step1 : ∠ a:b:c = ∠ b:c:d) := by euclid_apply (helper_1_34_step1 a b c d AB CD AC BD BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide c BD; assumption)) (by euclid_assumption "$AB$ is parallel to $CD$" (show ¬(AB.intersectsLine CD); assumption)) (by euclid_assumption "" (show ¬(AC.intersectsLine BD); assumption)) (by euclid_assumption "the straight-line $BC$ has fallen across  them" (show b.onLine AB ∧ b.onLine BC ∧ c.onLine CD ∧ c.onLine BC; assumption)))

  -- @assumption_valid
  have step2_assumption1 : ¬(AC.intersectsLine BD) := by assumption
  -- @assumption_valid
  have step2_assumption2 : c.onLine AC ∧ c.onLine BC ∧ b.onLine BD ∧ b.onLine BC := by euclid_finish
  -- @assumption ("$AC$ is parallel to $BD$", ¬(AC.intersectsLine BD))
  -- @assumption ("$BC$ has fallen across them", c.onLine AC ∧ c.onLine BC ∧ b.onLine BD ∧ b.onLine BC)
  euclid_sentence "1.34.2"
    "Again, since $AC$ is parallel to $BD$, and $BC$ has fallen across them, the alternate angles $ACB$ and $CBD$ are equal to one another [Prop.~1.29]. "
    (step2 : ∠ a:c:b = ∠ c:b:d) := by euclid_apply (helper_1_34_step2 a b c d AB CD AC BD BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide c BD; assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine CD); assumption)) (by euclid_assumption "$AC$ is parallel to $BD$" (show ¬(AC.intersectsLine BD); assumption)) (by euclid_assumption "$BC$ has fallen across them" (show c.onLine AC ∧ c.onLine BC ∧ b.onLine BD ∧ b.onLine BC; assumption)))

  -- @assumption_valid
  have step3_assumption1 : ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:a = ∠ c:b:d := by euclid_finish
  -- @assumption ("the two angles $ABC$ and $BCA$ equal to the two (angles) $BCD$ and $CBD$, respectively", ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:a = ∠ c:b:d)
  euclid_sentence "1.34.3"
    "So $ABC$ and $BCD$ are two triangles having the two angles $ABC$ and $BCA$ equal to the two (angles) $BCD$ and $CBD$, respectively, and one side equal to one side---the (one) by the equal angles and common to them, (namely) $BC$."
    (step3 : formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD) := by euclid_apply (helper_1_34_step3 a b c d AB CD AC BD BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide c BD; assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine CD); assumption)) (by euclid_assumption "" (show ¬(AC.intersectsLine BD); assumption)) (by euclid_assumption "the two angles $ABC$ and $BCA$ equal to the two (angles) $BCD$ and $CBD$, respectively" (show ∠ a:b:c = ∠ b:c:d ∧ ∠ b:c:a = ∠ c:b:d; assumption)))

  euclid_sentence "1.34.4"
    "Thus, they will also  have the remaining sides  equal to the corresponding remaining (sides), and the remaining angle (equal) to the remaining angle [Prop.~1.26]."
    (step4 : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b) := by euclid_apply (helper_1_34_step4 a b c d AB CD AC BD BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide c BD; assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine CD); assumption)) (by euclid_assumption "" (show ¬(AC.intersectsLine BD); assumption)) (by euclid_assumption "" (show ∠ a:b:c = ∠ b:c:d; assumption)) (by euclid_assumption "" (show ∠ a:c:b = ∠ c:b:d; assumption)) (by euclid_assumption "" (show formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD; assumption)))

  euclid_sentence "1.34.5"
    "Thus, side $AB$ is equal to $CD$,"
    (step5 : |(a─b)| = |(c─d)|) := by euclid_apply (helper_1_34_step5 a b c d AB CD AC BD BC (by euclid_assumption "" (show |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b; assumption)))

  euclid_sentence "1.34.6"
    "and $AC$ to $BD$."
    (step6 : |(a─c)| = |(b─d)|) := by euclid_apply (helper_1_34_step6 a b c d AB CD AC BD BC (by euclid_assumption "" (show |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b; assumption)))

  euclid_sentence "1.34.7"
    "Furthermore, angle $BAC$ is  equal to $CDB$."
    (step7 : ∠ b:a:c = ∠ c:d:b) := by euclid_apply (helper_1_34_step7 a b c d AB CD AC BD BC (by euclid_assumption "" (show |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b; assumption)))

  -- @assumption_valid
  have step8_assumption1 : ∠ a:b:c = ∠ b:c:d := by assumption
  -- @assumption_valid
  have step8_assumption2 : ∠ c:b:d = ∠ a:c:b := by linarith
  -- @assumption ("angle $ABC$ is equal to $BCD$", ∠ a:b:c = ∠ b:c:d)
  -- @assumption ("$CBD$ to $ACB$", ∠ c:b:d = ∠ a:c:b)
  euclid_sentence "1.34.8"
    "And since angle $ABC$ is equal to $BCD$, and $CBD$ to $ACB$, the whole (angle) $ABD$ is thus equal to the whole (angle) $ACD$."
    (step8 : ∠ a:b:d = ∠ a:c:d) := by euclid_apply (helper_1_34_step8 a b c d AB CD AC BD BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide c BD; assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine CD); assumption)) (by euclid_assumption "" (show ¬(AC.intersectsLine BD); assumption)) (by euclid_assumption "angle $ABC$ is equal to $BCD$" (show ∠ a:b:c = ∠ b:c:d; assumption)) (by euclid_assumption "" (show ∠ a:c:b = ∠ c:b:d; assumption)) (by euclid_assumption "angle $ABC$ is equal to $BCD$" (show ∠ a:b:c = ∠ b:c:d; assumption)) (by euclid_assumption "$CBD$ to $ACB$" (show ∠ c:b:d = ∠ a:c:b; assumption)))

  euclid_sentence "1.34.9"
    "And  $BAC$ was also shown  (to be) equal to $CDB$. "
    (step9 : ∠ b:a:c = ∠ c:d:b) := by euclid_apply (helper_1_34_step9 a b c d AB CD AC BD BC (by euclid_assumption "" (show |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ b:a:c = ∠ c:d:b; assumption)))

  euclid_sentence "1.34.10"
    "Thus, in parallelogrammic figures the opposite sides and angles are equal to one another. "
    (step10 : |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧ ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b) := by euclid_apply (helper_1_34_step10 a b c d AB CD AC BD BC (by euclid_assumption "" (show |(a─b)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(b─d)|; assumption)) (by euclid_assumption "" (show ∠ a:b:d = ∠ a:c:d; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∠ c:d:b; assumption)))

  euclid_wts "1.34.11"
    "And, I also say that a diagonal cuts them in half."

  -- @assumption ("$AB$ is equal to $CD$", |(a─b)| = |(c─d)|)
  -- @assumption ("$BC$ (is) common", distinctPointsOnLine b c BC)
  -- BC=CB is the common side of the SAS pairing; kept as its own conjunct per the sentence
  euclid_sentence "1.34.12"
    "For since $AB$ is equal to $CD$, and $BC$ (is) common, the two (straight-lines) $AB$, $BC$ are equal to the two (straight-lines) $DC$, $CB$, respectively."
    (step12 : |(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|) := by euclid_apply (helper_1_34_step12 a b c d AB CD AC BD BC (by euclid_assumption "" (show |(a─b)| = |(c─d)|; assumption)))

  euclid_sentence "1.34.13"
    "And angle $ABC$ is equal to angle $BCD$."
    (step13 : ∠ a:b:c = ∠ b:c:d) := by euclid_apply (helper_1_34_step13 a b c d AB CD AC BD BC (by euclid_assumption "" (show ∠ a:b:c = ∠ b:c:d; assumption)))

  euclid_sentence "1.34.14"
    "Thus, the base $AC$ (is) also equal to $DB$,"
    (step14 : |(a─c)| = |(d─b)|) := by euclid_apply (helper_1_34_step14 a b c d AB CD AC BD BC (by euclid_assumption "" (show |(a─c)| = |(b─d)|; assumption)))

  euclid_sentence "1.34.15"
    "and triangle $ABC$ is equal to triangle $BCD$ [Prop.~1.4]. "
    (step15 : Triangle.area △ a:b:c = Triangle.area △ b:c:d) := by euclid_apply (helper_1_34_step15 a b c d AB CD AC BD BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide c BD; assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine CD); assumption)) (by euclid_assumption "" (show ¬(AC.intersectsLine BD); assumption)) (by euclid_assumption "" (show formTriangle a b c AB BC AC ∧ formTriangle b c d BC CD BD; assumption)) (by euclid_assumption "" (show |(a─b)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∠ c:d:b; assumption)) (by euclid_assumption "" (show |(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(d─b)|; assumption)))

  euclid_sentence "1.34.16"
    "Thus, the diagonal $BC$ cuts the parallelogram $ACDB$ in half."
    (step16 : Triangle.area △ a:b:c = Triangle.area △ d:c:b) := by euclid_apply (helper_1_34_step16 a b c d AB CD AC BD BC (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ b:c:d; assumption)))

  exact ⟨step5, step6, step8, step7, step16⟩
  euclid_conclude_sentence "1.34.17"
    "(Which is) the very thing it was required to show."

end Elements.Book1
