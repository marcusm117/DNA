import SystemE
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.27 (sub): area of the whole square ADEB = |AB|².
-- rectangle_area on ADEB (formParallelogram d e a b DE AB AD BE), right angle ∠BAD = ∟:
-- area = |d─e|·|d─a| = |AB|·|AB|  (square sides |d─e| = |a─b| = |d─a|).
set_option systemE.solverTime 30 in
theorem helper_2_step27_bigsq (a b d e : Point) (AB DE AD BE : Line)
    (hbig : formParallelogram d e a b DE AB AD BE)
    (hde : |(d─e)| = |(a─b)|) (had : |(a─d)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) :
    Triangle.area △ d:a:b + Triangle.area △ d:b:e = |(a─b)| * |(a─b)| := by
  euclid_intros
  euclid_assert |(d─a)| = |(a─b)|
  euclid_apply (rectangle_area d e a b DE AB AD BE)
  euclid_finish

end Elements.Book2
