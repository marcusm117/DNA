import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.12 sub: area(ADHK) = |a─d| * |d─h|. ADHK is the rectangle (formParallelogram a d k h AB KM AK DG)
   with the right angle ∠ a:k:h = ∟, so rectangle_area gives area(△a:k:h + △a:d:h) = |a─d|·|a─k|;
   and |a─k| = |d─h| (opposite sides of the parallelogram [Prop.~1.34]); area △a:h:k = △a:k:h by
   permutation. Hence area △a:d:h + △a:h:k = |a─d|·|d─h|. -/
theorem helper_2_5_step12_rect (a d h k : Point) (AB KM AK DG : Line)
    (hpar : formParallelogram a d k h AB KM AK DG)
    (hakh : ∠ a:k:h = ∟) :
    Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─h)| := by
  euclid_intros
  -- opposite sides: |a─k| = |d─h|
  have hak_dh : |(a─k)| = |(d─h)| := by
    euclid_apply (proposition_34' a d k h AB KM AK DG)
    euclid_finish
  -- rectangle area: area △a:k:h + △a:d:h = |a─d|·|a─k|
  have hrect : Triangle.area △ a:k:h + Triangle.area △ a:d:h = |(a─d)| * |(a─k)| := by
    euclid_apply (rectangle_area a d k h AB KM AK DG)
    euclid_finish
  rw [hak_dh] at hrect
  euclid_finish

end Elements.Book2
