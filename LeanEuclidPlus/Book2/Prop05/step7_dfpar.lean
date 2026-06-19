import SystemE
import Book2.Prop05.step7_dfpar_dgbf
import Book2.Prop05.step7_dfpar_boff
import Book2.Prop05.step7_dfpar_goff
import Book2.Prop05.step7_dfpar_doff
import Book2.Prop05.step7_dfpar_ss
import Book2.Prop05.step7_dfpar_abef
import Book2.Prop05.step7_dfpar_body
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_5_step7_dfpar (b c d e f g : Point) (AB BF CE DG EF : Line)
    (hdDG : d.onLine DG) (hgDG : g.onLine DG)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hcCE : c.onLine CE) (hcAB : c.onLine AB)
    (hgEF : g.onLine EF) (hfEF : f.onLine EF) (heEF : e.onLine EF)
    (hEFAB : ¬(EF.intersectsLine AB))
    (hDGCE : ¬(DG.intersectsLine CE))
    (hCEBF : ¬(CE.intersectsLine BF))
    (hcdb : between c d b)
    (hbce : ∠b:c:e = ∟)
    (hcelen : |(c─e)| = |(c─b)|) :
    formParallelogram d g b f DG BF AB EF := by
  euclid_intros
  have step7_dfpar_dgbf : ¬(DG.intersectsLine BF) := by euclid_apply (helper_2_5_step7_dfpar_dgbf b c d AB BF CE DG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- @args: b c d e AB EF
  have step7_dfpar_boff : ¬(b.onLine EF) := by euclid_apply (helper_2_5_step7_dfpar_boff b c d e AB EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- @args: b c d f g AB BF DG EF
  have step7_dfpar_goff : ¬(g.onLine BF) := by euclid_apply (helper_2_5_step7_dfpar_goff b c d f g AB BF DG EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- @args: b c d e AB EF
  have step7_dfpar_doff : ¬(d.onLine EF) := by euclid_apply (helper_2_5_step7_dfpar_doff b c d e AB EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_dfpar_ss : d.sameSide b EF := by euclid_apply (helper_2_5_step7_dfpar_ss b d AB EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_dfpar_abef : ¬(AB.intersectsLine EF) := by euclid_apply (helper_2_5_step7_dfpar_abef AB EF (by assumption)); (try split_ands) <;> assumption
  have hgf : g ≠ f := fun heq => step7_dfpar_goff (heq ▸ hfBF)
  have step7_dfpar_body : formParallelogram d g b f DG BF AB EF := by euclid_apply (helper_2_5_step7_dfpar_body b d f g AB BF DG EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  exact step7_dfpar_body

end Elements.Book2
