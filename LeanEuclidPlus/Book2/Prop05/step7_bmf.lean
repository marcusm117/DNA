import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.7 sub: between b m f (m = KM ∩ BF lies between b and f on BF).
   Same figure as step6_bmf: b,f on BF with m = KM ∩ BF in between.
   Approach: b and f are on opposite sides of KM (KM ∥ AB, f on EF above, b on AB below);
   m is KM ∩ BF, so pasch_4 gives between b m f. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_bmf (b c d e f h m : Point) (AB BF BE EF CE DG KM : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hmBF : m.onLine BF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hhKM : h.onLine KM) (hmKM : m.onLine KM)
    (hhoffEF : ¬(h.onLine EF)) (hKMEF : ¬(KM.intersectsLine EF))
    (heoffDG : ¬(e.onLine DG)) (hboffDG : ¬(b.onLine DG))
    (hKMAB : ¬(KM.intersectsLine AB)) (hEFAB : ¬(EF.intersectsLine AB))
    (hCEBF : ¬(CE.intersectsLine BF)) (hDGCE : ¬(DG.intersectsLine CE))
    (hecBF : e.sameSide c BF) (hcdb : between c d b) :
    between b m f := by
  euclid_intros
  have step7_bmf_opp : ¬(b.sameSide f KM) := by euclid_finish
  euclid_apply (pasch_4 b m f KM BF)
  euclid_finish

end Elements.Book2
