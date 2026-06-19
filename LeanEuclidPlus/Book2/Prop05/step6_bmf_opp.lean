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
  have step6_bmf_bopp : ¬(b.sameSide e DG) := by euclid_apply (helper_2_5_step6_bmf_bopp b c d e AB CE DG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbe : b ≠ e := by euclid_finish
  have step6_bmf_bhe : between b h e := by euclid_apply (helper_2_5_step6_bmf_bhe b e h BE DG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step6_bmf_fse : f.sameSide e KM := by euclid_apply (helper_2_5_step6_bmf_fse e f h EF KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_apply (pasch_3 b h e KM)
  euclid_finish

end Elements.Book2
