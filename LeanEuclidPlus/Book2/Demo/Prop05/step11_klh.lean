import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: between k l h on line KM. Mirrors Prop06 step9_klm pattern. l = CE∩KM,
   k = AK∩KM (same side of CE as a since AK ∥ CE), h = DG∩KM (same side of CE as d since
   DG ∥ CE). a,d on opposite sides of CE (c between a,d on AB, c ∈ CE → pasch_3). Then
   pasch_4 on k,l,h across CE and KM gives between k l h. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_klh (a c d h k l : Point) (AB KM CE AK DG : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hacd : between a c d)
    (hssak : k.sameSide a CE) (hssdh : d.sameSide h CE)
    (hAKCE : ¬(AK.intersectsLine CE)) (hDGCE : ¬(DG.intersectsLine CE)) :
    between k l h := by
  euclid_intros
  euclid_apply (pasch_3 a c d CE)
  euclid_apply (pasch_4 k l h CE KM)
  euclid_finish

end Elements.Book2
