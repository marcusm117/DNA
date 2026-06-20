import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.11 sub: area(ADMK) = |a─d| · |d─m|. ADMK is the rectangle (formParallelogram a d k m AB KM AK DF)
   with the right corner ∠ a:k:m = ∟, so rectangle_area gives △a:k:m + △a:d:m = |a─d|·|a─k|; and
   |a─k| = |d─m| (opposite sides [Prop.~1.34]); △a:m:k = △a:k:m by permutation. Hence
   △a:d:m + △a:m:k = |a─d|·|d─m|. (Mirror of Prop05 step12_rect.) -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step11_rect (a d m k : Point) (AB KM AK DF : Line)
    (hpar : formParallelogram a d k m AB KM AK DF)
    (hakm : ∠ a:k:m = ∟) :
    Triangle.area △ a:d:m + Triangle.area △ a:m:k = |(a─d)| * |(d─m)| := by
  euclid_intros
  have hak_dm : |(a─k)| = |(d─m)| := by
    euclid_apply (proposition_34' a d k m AB KM AK DF)
    euclid_finish
  have hrect : Triangle.area △ a:k:m + Triangle.area △ a:d:m = |(a─d)| * |(a─k)| := by
    euclid_apply (rectangle_area a d k m AB KM AK DF)
    euclid_finish
  rw [hak_dm] at hrect
  euclid_finish

end Elements.Book2
