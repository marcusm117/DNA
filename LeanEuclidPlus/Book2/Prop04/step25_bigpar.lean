import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: the big square ADEB as formParallelogram b e a d BE AD AB DE (b,e on BE; a,d on AD;
   b,a on AB; e,d on DE; b.sameSide a DE; BE ∥ AD; AB ∥ DE). b.sameSide a DE (b,a on AB ∥ DE) +
   non-intersections + e ≠ d supplied. -/
theorem helper_2_4_step25_bigpar (b e a d : Point) (BE AD AB DE : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (heDE : e.onLine DE) (hdDE : d.onLine DE)
    (hBEAD : ¬(BE.intersectsLine AD)) (hABDE : ¬(AB.intersectsLine DE))
    (hbade : b.sameSide a DE) (hed : e ≠ d) :
    formParallelogram b e a d BE AD AB DE := by
  euclid_intros
  euclid_finish

end Elements.Book2
