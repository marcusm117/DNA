import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact: the square ADEB's parallelogram, formParallelogram d e a b DE AB AD BE, repackaged
   from the atoms the proposition_46 construction left in context. Minimal context so it is fast. -/
theorem helper_2_2_step5_hsq (a b d e : Point) (AB DE AD BE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (heb : e ≠ b) (hdsaBE : d.sameSide a BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE)) :
    formParallelogram d e a b DE AB AD BE := by
  euclid_intros
  euclid_finish

end Elements.Book2
