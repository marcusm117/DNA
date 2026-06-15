import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6: AL (= K,L,A,C) is a parallelogram. Top edge A,C on AB; bottom edge K,L on KM;
   left vertical AK (k,a); right vertical CE (l,c). The non-obvious conjunct k.sameSide a CE is passed
   in as a hypothesis (proved by step6_sska, a sibling node); the rest closes from the incidences. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step6_alpar (a c k l : Point) (AB KM AK CE : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (hlc : l ≠ c) (hska : k.sameSide a CE)
    (hKMAB : ¬(KM.intersectsLine AB)) (hAKCE : ¬(AK.intersectsLine CE)) :
    formParallelogram k l a c KM AB AK CE := by
  euclid_intros
  euclid_finish

end Elements.Book2
