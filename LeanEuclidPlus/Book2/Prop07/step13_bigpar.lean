import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: the whole square ADEB as formParallelogram a b d e AB DE AD BE (a,b on AB; d,e on DE;
   a,d on AD; b,e on BE; a.sameSide d BE; AB ∥ DE; AD ∥ BE). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_bigpar (a b d e : Point) (AB DE AD BE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hABDE : ¬(AB.intersectsLine DE)) (hADBE : ¬(AD.intersectsLine BE))
    (hasd : a.sameSide d BE) (hbe : b ≠ e) :
    formParallelogram a b d e AB DE AD BE := by
  euclid_intros
  euclid_finish

end Elements.Book2
