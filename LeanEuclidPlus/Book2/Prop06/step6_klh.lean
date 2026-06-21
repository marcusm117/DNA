import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6: the feet k, l, h on KM are in order between k l h, mirroring between a c b of
   their tops on AB. l ∈ CE ∩ KM; k, h are distinct points of KM. k shares a's side of CE
   (k.sameSide a CE = step6_sska), h shares b's side (b.sameSide h CE = step6_ssbh); a, b are on
   opposite sides of CE because c (on CE) is between a and b (pasch_3). Then pasch_4 on k, l, h across
   CE and KM gives between k l h. -/
theorem helper_2_6_step6_klh (a b c k l h : Point) (AB CE KM : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hacb : between a c b)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE)
    (hssak : k.sameSide a CE) (hssbh : b.sameSide h CE) :
    between k l h := by
  euclid_intros
  euclid_apply (pasch_3 a c b CE)
  euclid_apply (pasch_4 k l h CE KM)
  euclid_finish

end Elements.Book2
