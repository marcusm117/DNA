import SystemE

namespace Elements.Book2

/- 2.2.3: AE is the square on AB, area |a─b|·|a─b|. rectangle_area on the square. -/
set_option systemE.solverTime 30 in
theorem helper_2_step3 (a b d e : Point) (AB DE AD BE : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hde : |(d─e)| = |(a─b)|) (had : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟) :
    Triangle.area △ d:a:b + Triangle.area △ d:b:e = |(a─b)| * |(a─b)| := by
  euclid_intros
  euclid_apply (rectangle_area d e a b DE AB AD BE)
  have hda : |(d─a)| = |(a─b)| := by euclid_finish
  have hrw : |(a─b)| * |(a─b)| = |(d─e)| * |(d─a)| := by rw [hde, hda]
  rw [hrw]
  euclid_finish

end Elements.Book2
