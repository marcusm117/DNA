import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
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
  have step7_dfpar_dgbf : ¬(DG.intersectsLine BF) := by sorry
  -- @args: b c d e AB EF
  have step7_dfpar_boff : ¬(b.onLine EF) := by sorry
  -- @args: b c d f g AB BF DG EF
  have step7_dfpar_goff : ¬(g.onLine BF) := by sorry
  -- @args: b c d e AB EF
  have step7_dfpar_doff : ¬(d.onLine EF) := by sorry
  have step7_dfpar_ss : d.sameSide b EF := by sorry
  have step7_dfpar_abef : ¬(AB.intersectsLine EF) := by sorry
  have hgf : g ≠ f := fun heq => step7_dfpar_goff (heq ▸ hfBF)
  have step7_dfpar_body : formParallelogram d g b f DG BF AB EF := by sorry
  exact step7_dfpar_body

end Elements.Book2
