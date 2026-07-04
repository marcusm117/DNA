import SystemE
import Book1.Prop15.step1
import Book1.Prop15.step2
import Book1.Prop15.step3
import Book1.Prop15.step4
import Book1.Prop15.step5
import Book1.Prop15.step6
import Book1.Prop15.step7
import Book1.Prop15.h1
import Book1.Prop15.h2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
--map done
theorem proposition_15 : ∀ (a b c d e : Point) (AB CD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧
  CD ≠ AB ∧ (between d e c) ∧ (between a e b) →
  (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d) := by
  euclid_intros
  euclid_intro_sentence "1.15.0"
    "If two straight-lines cut one another then they make the vertically opposite angles equal to one another.  For let the two straight-lines $AB$ and $CD$ cut one another at the point $E$. I say that  angle $AEC$ is equal to (angle) $DEB$, and (angle) $CEB$ to (angle) $AED$. "

  -- @assumption_valid
  have step1_assumption1 : between d e c := by assumption
  -- @assumption ("the straight-line $AE$ stands on the straight-line $CD$", between d e c)
  euclid_sentence "1.15.1"
    "For since the straight-line $AE$ stands on the straight-line $CD$, making the angles $CEA$ and $AED$, the (sum of the) angles $CEA$ and $AED$ is thus equal to two right-angles [Prop.~1.13]."
    (step1 : ∠ c:e:a + ∠ a:e:d = ∟ + ∟) := by euclid_apply (helper_1_15_step1 a b c d e AB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine CD; assumption)) (by euclid_assumption "" (show CD ≠ AB; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "the straight-line $AE$ stands on the straight-line $CD$" (show between d e c; assumption)))

  -- @assumption_valid
  have step2_assumption1 : between a e b := by assumption
  -- @assumption ("the straight-line $DE$ stands on the straight-line $AB$, making the angles $AED$ and $DEB$", between a e b)
  euclid_sentence "1.15.2"
    "Again, since the straight-line $DE$ stands on the straight-line $AB$, making the angles $AED$ and $DEB$, the (sum of the) angles $AED$ and $DEB$ is thus equal to two right-angles [Prop.~1.13]."
    (step2 : ∠ a:e:d + ∠ d:e:b = ∟ + ∟) := by euclid_apply (helper_1_15_step2 a b d e AB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show e.onLine CD; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show CD ≠ AB; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "the straight-line $DE$ stands on the straight-line $AB$, making the angles $AED$ and $DEB$" (show between a e b; assumption)))

  euclid_sentence "1.15.3"
    "But (the sum of) $CEA$ and $AED$ was also shown (to be) equal to two right-angles."
    (step3 : ∠ c:e:a + ∠ a:e:d = ∟ + ∟) := by euclid_apply (helper_1_15_step3 c e a d (by euclid_assumption "" (show ∠ c:e:a + ∠ a:e:d = ∟ + ∟; assumption)))

  euclid_sentence "1.15.4"
    "Thus, (the sum of) $CEA$ and $AED$ is equal to (the sum of) $AED$ and $DEB$ [C.N.~1]."
    (step4 : ∠ c:e:a + ∠ a:e:d = ∠ a:e:d + ∠ d:e:b) := by euclid_apply (helper_1_15_step4 c e a d b (by euclid_assumption "" (show ∠ c:e:a + ∠ a:e:d = ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ a:e:d + ∠ d:e:b = ∟ + ∟; assumption)))

  euclid_sentence "1.15.5"
    "Let $AED$ have been subtracted from both."
    (step5 : ∠ c:e:a + ∠ a:e:d - ∠ a:e:d = ∠ a:e:d + ∠ d:e:b - ∠ a:e:d) := by euclid_apply (helper_1_15_step5 c e a d b (by euclid_assumption "" (show ∠ c:e:a + ∠ a:e:d = ∠ a:e:d + ∠ d:e:b; assumption)))

  euclid_sentence "1.15.6"
    "Thus, the remainder $CEA$ is equal to the remainder $BED$ [C.N.~3]."
    (step6 : ∠ c:e:a = ∠ b:e:d) := by euclid_apply (helper_1_15_step6 c e a d b (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show ∠ c:e:a + ∠ a:e:d - ∠ a:e:d = ∠ a:e:d + ∠ d:e:b - ∠ a:e:d; assumption)))

  euclid_sentence "1.15.7"
    "Similarly, it can be shown that $CEB$ and $DEA$ are also equal. "
    (step7 : ∠ c:e:b = ∠ d:e:a) := by euclid_apply (helper_1_15_step7 a b c d e AB CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine CD; assumption)) (by euclid_assumption "" (show CD ≠ AB; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show ∠ a:e:d + ∠ d:e:b = ∟ + ∟; assumption)))

  have h1 : ∠ a:e:c = ∠ d:e:b := by euclid_apply (helper_1_15_h1 a e c d b (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show ∠ c:e:a = ∠ b:e:d; assumption)))
  have h2 : ∠ c:e:b = ∠ a:e:d := by euclid_apply (helper_1_15_h2 c e b d a (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show ∠ c:e:b = ∠ d:e:a; assumption)))
  exact ⟨h1, h2⟩
  euclid_conclude_sentence "1.15.8"
    "Thus, if two straight-lines cut one another then they make the vertically opposite angles equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
