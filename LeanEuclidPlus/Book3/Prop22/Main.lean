import SystemE
import Book3.Prop22.step1
import Book3.Prop22.step2
import Book3.Prop22.step3
import Book3.Prop22.step4
import Book3.Prop22.step5
import Book3.Prop22.step6
import Book3.Prop22.step7
import Book3.Prop22.step8
import Book3.Prop22.step9
import Book3.Prop22.step2_assumption1
import Book3.Prop22.step3_assumption1
import Book3.Prop22.step4_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_22 : ∀ (a b c d : Point) (ABCD : Circle) (AC BD : Line),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  b.opposingSides d AC ∧ a.opposingSides c BD →
  (∠ d:a:b + ∠ b:c:d = ∟ + ∟) ∧ (∠ a:b:c + ∠ c:d:a = ∟ + ∟) :=
by
  euclid_intros
  euclid_intro_sentence "3.22.0"
    "For quadrilaterals within circles, the (sum of the) opposite angles is equal to two right-angles. Let $ABCD$ be a circle, and let $ABCD$ be a quadrilateral within it. I say that the (sum of the) opposite angles is equal to two right-angles."

  euclid_sentence "3.22.1"
    "Let $AC$ and $BD$ be joined."
    (step1 : distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD) := by euclid_apply (helper_3_22_step1 a b c d AC BD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)))

  -- @assumption_gap
  have step2_assumption1 : ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟ := by euclid_apply (helper_3_22_step2_assumption1 a b c AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)))
  -- @assumption ("the three angles of any triangle are equal to two right-angles", ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟)
  euclid_sentence "3.22.2"
    "Therefore, since the three angles of any triangle are equal to two right-angles [Prop.~1.32], the three angles $CAB$, $ABC$, and $BCA$ of triangle $ABC$ are thus equal to two right-angles."
    (step2 : ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟) := by euclid_apply (helper_3_22_step2 a b c AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "the three angles of any triangle are equal to two right-angles" (show ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟; assumption)))

  -- @assumption_gap
  have step3_assumption1 : ∃ (BC : Line), distinctPointsOnLine b c BC ∧ a.sameSide d BC := by euclid_apply (helper_3_22_step3_assumption1 a b c d AC BD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.sameSide d AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide c BD; assumption)))
  -- @assumption ("they are in the same segment $BADC$", ∃ (BC : Line), distinctPointsOnLine b c BC ∧ a.sameSide d BC)
  euclid_sentence "3.22.3"
    "And $CAB$ (is) equal to $BDC$. For they are in the same segment $BADC$ [Prop.~3.21]."
    (step3 : ∠ c:a:b = ∠ b:d:c) := by euclid_apply (helper_3_22_step3 a b c d ABCD (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "they are in the same segment $BADC$" (show ∃ (BC : Line), distinctPointsOnLine b c BC ∧ a.sameSide d BC; assumption)))

  -- @assumption_gap
  have step4_assumption1 : ∃ (AB₀ : Line), distinctPointsOnLine a b AB₀ ∧ c.sameSide d AB₀ := by euclid_apply (helper_3_22_step4_assumption1 a b c d AC BD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.sameSide d AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide c BD; assumption)))
  -- @assumption ("they are in the same segment $ADCB$", ∃ (AB₀ : Line), distinctPointsOnLine a b AB₀ ∧ c.sameSide d AB₀)
  euclid_sentence "3.22.4"
    "And $ACB$ (is equal) to $ADB$. For they are in the same segment $ADCB$ [Prop.~3.21]."
    (step4 : ∠ a:c:b = ∠ a:d:b) := by euclid_apply (helper_3_22_step4 a b c d ABCD (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "they are in the same segment $ADCB$" (show ∃ (AB₀ : Line), distinctPointsOnLine a b AB₀ ∧ c.sameSide d AB₀; assumption)))

  euclid_sentence "3.22.5"
    "Thus, the whole of $ADC$ is equal to $BAC$ and $ACB$."
    (step5 : ∠ a:d:c = ∠ b:a:c + ∠ a:c:b) := by euclid_apply (helper_3_22_step5 a b c d AC BD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.sameSide d AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide c BD; assumption)) (by euclid_assumption "" (show ∠ c:a:b = ∠ b:d:c; assumption)) (by euclid_assumption "" (show ∠ a:c:b = ∠ a:d:b; assumption)))

  euclid_sentence "3.22.6"
    "Let $ABC$ be added to both."
    (step6 : ∠ a:b:c + ∠ a:d:c = ∠ a:b:c + ∠ b:a:c + ∠ a:c:b) := by euclid_apply (helper_3_22_step6 a b c d (by euclid_assumption "" (show ∠ a:d:c = ∠ b:a:c + ∠ a:c:b; assumption)))

  euclid_sentence "3.22.7"
    "Thus, $ABC$, $BAC$, and $ACB$ are equal to $ABC$ and $ADC$."
    (step7 : ∠ a:b:c + ∠ b:a:c + ∠ a:c:b = ∠ a:b:c + ∠ a:d:c) := by euclid_apply (helper_3_22_step7 a b c d (by euclid_assumption "" (show ∠ a:b:c + ∠ a:d:c = ∠ a:b:c + ∠ b:a:c + ∠ a:c:b; assumption)))

  -- @assumption_valid
  have step8_assumption1 : ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟ := by assumption
  -- @assumption ("$ABC$, $BAC$, and $ACB$ are equal to two right-angles", ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟)
  euclid_sentence "3.22.8"
    "But, $ABC$, $BAC$, and $ACB$ are equal to two right-angles. Thus, $ABC$ and $ADC$ are also equal to two right-angles."
    (step8 : ∠ a:b:c + ∠ c:d:a = ∟ + ∟) := by euclid_apply (helper_3_22_step8 a b c d AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine AC; assumption)) (by euclid_assumption "" (show ∠ a:b:c + ∠ b:a:c + ∠ a:c:b = ∠ a:b:c + ∠ a:d:c; assumption)) (by euclid_assumption "$ABC$, $BAC$, and $ACB$ are equal to two right-angles" (show ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟; assumption)))

  euclid_sentence "3.22.9"
    "Similarly, we can show that angles $BAD$ and $DCB$ are also equal to two right-angles."
    (step9 : ∠ d:a:b + ∠ b:c:d = ∟ + ∟) := by euclid_apply (helper_3_22_step9 a b c d AC BD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.sameSide d AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide c BD; assumption)) (by euclid_assumption "" (show ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:c + ∠ c:d:a = ∟ + ∟; assumption)))

  exact ⟨step9, step8⟩
  euclid_conclude_sentence "3.22.10"
    "Thus, for quadrilaterals within circles, the (sum of the) opposite angles is equal to two right-angles. (Which is) the very thing it was required to show."

end Elements.Book3
