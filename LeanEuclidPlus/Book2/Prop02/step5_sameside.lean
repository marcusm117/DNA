import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.5: a.sameSide d CF. Given the square ADEB's parallelogram (step5_hsq:
   formParallelogram d e a b DE AB AD BE) the SMT places a and d (both on the vertical AD, which
   does not cross CF) on the same side of CF in one step. -/
theorem helper_2_2_step5_sameside (a b c d e : Point) (AB DE AD BE CF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCF : c.onLine CF)
    (heb : e ≠ b) (hdsaBE : d.sameSide a BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) :
    a.sameSide d CF := by
  euclid_intros
  have step5_hsq : formParallelogram d e a b DE AB AD BE := by sorry
  euclid_finish

end Elements.Book2
