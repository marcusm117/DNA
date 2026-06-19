import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub (ORPHAN — no longer used as a backed node; step8_cmpar_flip_lss not needed since
   hcmpar in step8.lean provides the formParallelogram directly). Kept for reference. -/
theorem helper_2_5_step8_cmpar_flip (b c l m : Point) (AB KM CE BF : Line)
    (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (hmBF : m.onLine BF) (hbBF : b.onLine BF)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hCEBF : ¬(CE.intersectsLine BF)) :
    formParallelogram l m c b KM AB CE BF := by
  euclid_intros
  euclid_finish

end Elements.Book2
