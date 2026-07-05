import SystemE
import Book.Prop31
import Book1.Prop32.step1
import Book1.Prop32.step2
import Book1.Prop32.step3
import Book1.Prop32.step4
import Book1.Prop32.step5
import Book1.Prop32.step6
import Book1.Prop32.step7
import Book1.Prop32.step8
import Book1.Prop32.step9
import Book1.Prop32.hgoal1
import Book1.Prop32.hgoal2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

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
    (step1 : c.onLine CE ∧ e.onLine CE ∧ ¬(CE.intersectsLine AB)) := by euclid_apply (helper_1_32_step1 c e AB CE (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬CE.intersectsLine AB; assumption)))

  -- @assumption_valid
  have step2_assumption1 : ¬(AB.intersectsLine CE) := by euclid_finish
  -- @assumption_valid
  have step2_assumption2 : distinctPointsOnLine a c AC := by euclid_finish
  -- @assumption ("$AB$ is parallel to $CE$", ¬(AB.intersectsLine CE))
  -- @assumption ("$AC$ has fallen across them", distinctPointsOnLine a c AC)
  euclid_sentence "1.32.2"
    "And since $AB$ is parallel to $CE$, and $AC$ has fallen across them, the alternate angles $BAC$ and $ACE$ are equal to one another [Prop.~1.29]."
    (step2 : ∠ b:a:c = ∠ a:c:e) := by euclid_apply (helper_1_32_step2 a b c e AB BC AC CE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬CE.intersectsLine AB; assumption)) (by euclid_assumption "" (show e.sameSide a BC; assumption)) (by euclid_assumption "$AB$ is parallel to $CE$" (show ¬(AB.intersectsLine CE); assumption)) (by euclid_assumption "$AC$ has fallen across them" (show distinctPointsOnLine a c AC; assumption)))

  -- @assumption_valid
  have step3_assumption1 : ¬(AB.intersectsLine CE) := by assumption
  -- @assumption_valid
  have step3_assumption2 : distinctPointsOnLine b d BC := by euclid_finish
  -- @assumption ("$AB$ is parallel to $CE$", ¬(AB.intersectsLine CE))
  -- @assumption ("the straight-line $BD$ has fallen across them", distinctPointsOnLine b d BC)
  euclid_sentence "1.32.3"
    "Again, since $AB$ is parallel to $CE$, and the straight-line $BD$ has fallen across them,  the external angle $ECD$ is equal to the internal and opposite (angle) $ABC$ [Prop.~1.29]."
    (step3 : ∠ e:c:d = ∠ a:b:c) := by euclid_apply (helper_1_32_step3 a b c d e AB BC AC CE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show between b c d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬CE.intersectsLine AB; assumption)) (by euclid_assumption "" (show e.sameSide a BC; assumption)) (by euclid_assumption "$AB$ is parallel to $CE$" (show ¬(AB.intersectsLine CE); assumption)) (by euclid_assumption "the straight-line $BD$ has fallen across them" (show distinctPointsOnLine b d BC; assumption)))

  euclid_sentence "1.32.4"
    "But $ACE$ was also shown (to be) equal to $BAC$."
    (step4 : ∠ a:c:e = ∠ b:a:c) := by euclid_apply (helper_1_32_step4 a b c e AB BC AC CE (by euclid_assumption "" (show ∠ b:a:c = ∠ a:c:e; assumption)))

  euclid_sentence "1.32.5"
    "Thus, the whole angle $ACD$ is equal to the (sum of the) two internal and opposite (angles) $BAC$ and $ABC$. "
    (step5 : ∠ a:c:d = ∠ b:a:c + ∠ a:b:c) := by euclid_apply (helper_1_32_step5 a b c d e AB BC AC CE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between b c d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬CE.intersectsLine AB; assumption)) (by euclid_assumption "" (show e.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CE; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a c AC; assumption)) (by euclid_assumption "" (show distinctPointsOnLine b d BC; assumption)))

  euclid_sentence "1.32.6"
    "Let $ACB$ have been added to both."
    (step6 : ∠ a:c:d + ∠ a:c:b = ∠ b:a:c + ∠ a:b:c + ∠ a:c:b) := by euclid_apply (helper_1_32_step6 a b c d AB BC AC (by euclid_assumption "" (show ∠ a:c:d = ∠ b:a:c + ∠ a:b:c; assumption)))

  euclid_sentence "1.32.7"
    "Thus, (the sum of) $ACD$ and $ACB$ is equal to the (sum of the) three (angles) $ABC$, $BCA$, and $CAB$."
    (step7 : ∠ a:c:d + ∠ a:c:b = ∠ a:b:c + ∠ b:c:a + ∠ c:a:b) := by euclid_apply (helper_1_32_step7 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ a:c:d + ∠ a:c:b = ∠ b:a:c + ∠ a:b:c + ∠ a:c:b; assumption)))

  euclid_sentence "1.32.8"
    "But, (the sum of) $ACD$ and $ACB$ is equal to two right-angles [Prop.~1.13]."
    (step8 : ∠ a:c:d + ∠ a:c:b = ∟ + ∟) := by euclid_apply (helper_1_32_step8 a b c d AB BC AC (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show between b c d; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a c AC; assumption)) (by euclid_assumption "" (show distinctPointsOnLine b d BC; assumption)))

  euclid_sentence "1.32.9"
    "Thus, (the sum of) $ACB$, $CBA$, and $CAB$ is also equal to two right-angles. "
    (step9 : ∠ a:c:b + ∠ c:b:a + ∠ c:a:b = ∟ + ∟) := by euclid_apply (helper_1_32_step9 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ a:c:d + ∠ a:c:b = ∠ a:b:c + ∠ b:c:a + ∠ c:a:b; assumption)) (by euclid_assumption "" (show ∠ a:c:d + ∠ a:c:b = ∟ + ∟; assumption)))

  have hgoal1 : ∠ a:c:d = ∠ c:a:b + ∠ a:b:c := by euclid_apply (helper_1_32_hgoal1 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∠ b:a:c + ∠ a:b:c; assumption)))
  have hgoal2 : ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟ := by euclid_apply (helper_1_32_hgoal2 a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ a:c:b + ∠ c:b:a + ∠ c:a:b = ∟ + ∟; assumption)))
  exact ⟨hgoal1, hgoal2⟩
  euclid_conclude_sentence "1.32.10"
    "Thus, in any triangle,  (if) one of the sides  (is) produced (then) the external angle is equal to the (sum of the) two internal and opposite (angles), and the (sum of the) three internal angles of the triangle is equal to two right-angles. (Which is) the very thing it was required to show."

end Elements.Book1
