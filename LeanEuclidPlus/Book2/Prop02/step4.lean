import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- 2.2.4: AE is the square on AB. The square ADEB (formParallelogram d e a b DE AB AD BE) with
   right angle ∠b:a:d; rectangle_area gives △e:d:a + △e:b:a = |d─e|*|d─a|, and the edges
   |d─e| = |a─b|, |d─a| = |a─d| = |a─b|, giving |a─b|*|a─b|. -/
theorem helper_2_2_step4 (a b d e : Point) (AB DE AD BE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (had : |(a─d)| = |(a─b)|) (hde : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟)
    (hdsaBE : d.sameSide a BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE)) (heb : e ≠ b) :
    Triangle.area △ a:d:e + Triangle.area △ a:b:e = |(a─b)| * |(a─b)| := by
  euclid_intros
  euclid_apply (rectangle_area d e a b DE AB AD BE)
  have hde2 : |(d─e)| = |(a─b)| := hde
  have hda : |(d─a)| = |(a─b)| := by euclid_finish
  have hprod : |(a─b)| * |(a─b)| = |(d─e)| * |(d─a)| := by rw [hde2, hda]
  rw [hprod]
  euclid_finish

end Elements.Book2
