import SystemE
import Book1.Prop43.step1
import Book1.Prop43.step2
import Book1.Prop43.step3
import Book1.Prop43.step4
import Book1.Prop43.step5
import Book1.Prop43.step6
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_43 : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  (Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) := by
  euclid_intros
  euclid_intro_sentence "1.43.0"
    "For any parallelogram, the complements of the parallelograms about the diagonal are equal to one another. Let $ABCD$ be a parallelogram, and $AC$ its diagonal. And let $EH$ and $FG$ be the parallelograms about  $AC$, and $BK$ and $KD$ the so-called complements (about $AC$). I say that the complement $BK$ is equal to the complement $KD$. "

  -- @assumption_valid
  have step1_assumption1 : formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC := by euclid_finish
  -- @assumption ("$ABCD$ is a parallelogram, and $AC$ its diagonal", formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC)
  euclid_sentence "1.43.1"
    "For since $ABCD$ is a parallelogram, and $AC$ its diagonal,  triangle $ABC$ is equal to triangle $ACD$ [Prop.~1.34]."
    (step1 : Triangle.area △ a:b:c = Triangle.area △ a:c:d) := by euclid_apply (helper_1_43_step1 a b c d AD BC AB CD AC (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "$ABCD$ is a parallelogram, and $AC$ its diagonal" (show formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC; assumption)))

  -- @assumption_valid
  have step2_assumption1 : formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC := by euclid_finish
  -- @assumption ("$EH$ is a parallelogram, and $AK$ is its diagonal", formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC)
  euclid_sentence "1.43.2"
    "Again, since $EH$ is a parallelogram, and $AK$ is its diagonal, triangle $AEK$ is equal to triangle $AHK$ [Prop.~1.34]."
    (step2 : Triangle.area △ a:e:k = Triangle.area △ a:h:k) := by euclid_apply (helper_1_43_step2 a e k h AD EF AB GH AC (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show k.onLine EF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show h ≠ k; assumption)) (by euclid_assumption "" (show a.sameSide e GH; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine EF; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine GH; assumption)) (by euclid_assumption "$EH$ is a parallelogram, and $AK$ is its diagonal" (show formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC; assumption)))

  euclid_sentence "1.43.3"
    "So, for the same (reasons), triangle $KFC$ is also equal to (triangle) $KGC$."
    (step3 : Triangle.area △ k:f:c = Triangle.area △ k:g:c) := by euclid_apply (helper_1_43_step3 k f g c EF BC GH CD AC (by euclid_assumption "" (show k.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show f.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show f ≠ c; assumption)) (by euclid_assumption "" (show k.sameSide g CD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine CD; assumption)) (by euclid_assumption "" (show k.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)))

  -- @assumption_valid
  have step4_assumption1 : Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧ Triangle.area △ k:f:c = Triangle.area △ k:g:c := by euclid_finish
  -- @assumption ("triangle $AEK$ is equal to triangle $AHK$, and $KFC$ to $KGC$", Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧ Triangle.area △ k:f:c = Triangle.area △ k:g:c)
  euclid_sentence "1.43.4"
    "Therefore, since triangle $AEK$ is equal to triangle $AHK$, and $KFC$ to $KGC$, triangle $AEK$ plus $KGC$ is equal to triangle $AHK$ plus $KFC$."
    (step4 : Triangle.area △ a:e:k + Triangle.area △ k:g:c = Triangle.area △ a:h:k + Triangle.area △ k:f:c) := by euclid_apply (helper_1_43_step4 a e k g h f c (by euclid_assumption "triangle $AEK$ is equal to triangle $AHK$, and $KFC$ to $KGC$" (show Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧ Triangle.area △ k:f:c = Triangle.area △ k:g:c; assumption)) (by euclid_assumption "" (show Triangle.area △ a:e:k = Triangle.area △ a:h:k; assumption)) (by euclid_assumption "" (show Triangle.area △ k:f:c = Triangle.area △ k:g:c; assumption)))

  euclid_sentence "1.43.5"
    "And the whole triangle $ABC$ is also equal to the whole (triangle) $ADC$."
    (step5 : Triangle.area △ a:b:c = Triangle.area △ a:d:c) := by euclid_apply (helper_1_43_step5 a b c d (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ a:c:d; assumption)))

  euclid_sentence "1.43.6"
    "Thus, the remaining complement $BK$ is equal to the remaining complement $KD$. "
    (step6 : Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) := by euclid_apply (helper_1_43_step6 a b c d e f g h k AD BC AB CD AC EF GH (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show g.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show f.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show k.onLine AC; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show k.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show h ≠ k; assumption)) (by euclid_assumption "" (show f ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show a.sameSide e GH; assumption)) (by euclid_assumption "" (show k.sameSide g CD; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show ¬AD.intersectsLine EF; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine GH; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine CD; assumption)) (by euclid_assumption "" (show between a h d; assumption)) (by euclid_assumption "" (show Triangle.area △ a:e:k + Triangle.area △ k:g:c = Triangle.area △ a:h:k + Triangle.area △ k:f:c; assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:c = Triangle.area △ a:d:c; assumption)))

  exact step6
  euclid_conclude_sentence "1.43.7"
    "Thus, for any parallelogramic figure, the complements of the parallelograms about the diagonal are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
