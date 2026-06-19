import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub-sub: k.sameSide e AB. k is on KM (∥ AB), e is on EF (∥ AB); both lines lie on the
   same side of AB and don't meet it, so k and e are on the same side of AB. (l on KM∩CE ties the
   figure together.) Proven via off-line facts + non-intersection of KM, EF with AB. -/
theorem helper_2_5_step8_kal_right_kse (a b c e k l : Point) (AB KM EF CE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM)
    (heEF : e.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    k.sameSide e AB := by
  euclid_intros
  euclid_finish

end Elements.Book2
