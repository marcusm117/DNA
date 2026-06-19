import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub (ORPHAN — no longer used as a backed node; step8_alpar_kss is used directly in step8.lean):
   formParallelogram k l a c KM AB AK CE (rectangle AL). Kept for reference. -/
theorem helper_2_5_step8_alpar (a c k l : Point) (AB KM AK CE : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (hKMAB : ¬(KM.intersectsLine AB)) (hAKCE : ¬(AK.intersectsLine CE)) :
    formParallelogram k l a c KM AB AK CE := by
  euclid_intros
  euclid_finish

end Elements.Book2
