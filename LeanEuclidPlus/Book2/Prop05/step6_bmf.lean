import SystemE
import Book2.Prop05.step6_bmf_opp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: between b m f (m = KM ∩ BF lies between side-BF endpoints b and f). h (= KM ∩ BE) is
   between b and e on the diagonal (sub-leaf step6_bmf_bhe), so pasch_3 b h e KM gives b,e on opposite
   sides of KM. f is on EF; with the figure incidences euclid_finish places f on e's side of KM, so
   b,f are opposite and pasch_4 b m f KM BF gives between b m f. -/
theorem helper_2_5_step6_bmf (b c d e f h m : Point) (AB BF BE EF CE DG KM : Line)
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
  -- b,f on opposite sides of KM (sub-leaf), m = KM ∩ BF, b ≠ f ⟹ pasch_4 places m between.
  have step6_bmf_opp : ¬(b.sameSide f KM) := by euclid_apply (helper_2_5_step6_bmf_opp b c d e f h AB BE CE DG EF KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_apply (pasch_4 b m f KM BF)
  euclid_finish

end Elements.Book2
