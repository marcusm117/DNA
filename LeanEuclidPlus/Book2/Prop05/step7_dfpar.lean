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
  have step7_dfpar_dgbf : ¬(DG.intersectsLine BF) := by euclid_apply (helper_2_5_step7_dfpar_dgbf b c d AB BF CE DG (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show between c d b; assumption)))
  -- @args: b c d e AB EF
  have step7_dfpar_boff : ¬(b.onLine EF) := by euclid_apply (helper_2_5_step7_dfpar_boff b c d e AB EF (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show ∠b:c:e = ∟; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
  -- @args: b c d f g AB BF DG EF
  have step7_dfpar_goff : ¬(g.onLine BF) := by euclid_apply (helper_2_5_step7_dfpar_goff b c d f g AB BF DG EF (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(b.onLine EF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine BF); assumption)))
  -- @args: b c d e AB EF
  have step7_dfpar_doff : ¬(d.onLine EF) := by euclid_apply (helper_2_5_step7_dfpar_doff b c d e AB EF (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show ∠b:c:e = ∟; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
  have step7_dfpar_ss : d.sameSide b EF := by euclid_apply (helper_2_5_step7_dfpar_ss b d AB EF (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ¬(d.onLine EF); assumption)) (by euclid_assumption "" (show ¬(b.onLine EF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
  have step7_dfpar_abef : ¬(AB.intersectsLine EF) := by euclid_apply (helper_2_5_step7_dfpar_abef AB EF (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
  have hgf : g ≠ f := fun heq => step7_dfpar_goff (heq ▸ hfBF)
  have step7_dfpar_body : formParallelogram d g b f DG BF AB EF := by euclid_apply (helper_2_5_step7_dfpar_body b d f g AB BF DG EF (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g ≠ f; assumption)) (by euclid_assumption "" (show d.sameSide b EF; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine EF); assumption)))
  exact step7_dfpar_body

end Elements.Book2
