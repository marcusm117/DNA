import SystemE
import Book2.Prop05.step6_bmf_bopp
import Book2.Prop05.step6_bmf_bhe
import Book2.Prop05.step6_bmf_fse
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub-sub: ¬b.sameSide f KM (b and f are on opposite sides of KM). h (= KM ∩ BE) is between b
   and e on the diagonal (sub-leaf step6_bmf_bhe), so pasch_3 b h e KM gives b,e opposite across KM.
   f shares e's side (f.sameSide e KM, sub-leaf step6_bmf_fse). Opposite-of-same ⟹ b,f opposite. -/
theorem helper_2_5_step6_bmf_opp (b c d e f h : Point) (AB BE CE DG EF KM : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hhKM : h.onLine KM)
    (hhoffEF : ¬(h.onLine EF)) (hKMEF : ¬(KM.intersectsLine EF))
    (heoffDG : ¬(e.onLine DG)) (hboffDG : ¬(b.onLine DG))
    (hKMAB : ¬(KM.intersectsLine AB)) (hEFAB : ¬(EF.intersectsLine AB))
    (hcdb : between c d b) (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(b.sameSide f KM) := by
  euclid_intros
  have step6_bmf_bopp : ¬(b.sameSide e DG) := by euclid_apply (helper_2_5_step6_bmf_bopp b c d e AB CE DG (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  have hbe : b ≠ e := by euclid_finish
  have step6_bmf_bhe : between b h e := by euclid_apply (helper_2_5_step6_bmf_bhe b e h BE DG (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show ¬(e.onLine DG); assumption)) (by euclid_assumption "" (show ¬(b.onLine DG); assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show ¬(b.sameSide e DG); assumption)))
  have step6_bmf_fse : f.sameSide e KM := by euclid_apply (helper_2_5_step6_bmf_fse e f h EF KM (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine EF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine EF); assumption)))
  euclid_apply (pasch_3 b h e KM)
  euclid_finish

end Elements.Book2
