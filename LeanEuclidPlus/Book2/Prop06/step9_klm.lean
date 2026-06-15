import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.9 sub: between k l m (the KM feet in order, mirroring a, c, d on AB). l = CE ∩ KM; k, m are
   distinct points of KM. k shares a's side of CE (step6_sska: k.sameSide a CE), m shares d's side
   (step9_ssdm: d.sameSide m CE); a, d are on opposite sides of CE because c (on CE) is between a and
   d (step9_acd via between a c d). Then pasch_4 on k, l, m across CE and KM gives between k l m. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step9_klm (a c d k l m : Point) (AB CE KM : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacd : between a c d)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE)
    (hssak : k.sameSide a CE) (hssdm : d.sameSide m CE) :
    between k l m := by
  euclid_intros
  euclid_apply (pasch_3 a c d CE)
  euclid_apply (pasch_4 k l m CE KM)
  euclid_finish

end Elements.Book2
