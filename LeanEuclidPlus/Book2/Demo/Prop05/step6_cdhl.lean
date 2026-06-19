import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: complement parallelogram CDHL = formParallelogram c d l h AB KM CE DG. (Mirror of Prop06
   step7_cbhl under relabel b→d, BG→DG.) def a b c d AB CD AC BD: a=c,b=d on AB; c=l,d=h on KM;
   a=c,c=l on CE; b=d,d=h on DG. sameSide c.sameSide l DG (step6_cdhl_ss); d ≠ h from d ∈ AB, ¬h ∈ AB
   (step6_hoffab). Parallels AB∥KM, CE∥DG in hand. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_cdhl (c d h l : Point) (AB KM CE DG : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hhoffAB : ¬(h.onLine AB)) (hsscl : c.sameSide l DG)
    (hKMAB : ¬(KM.intersectsLine AB)) (hDGCE : ¬(DG.intersectsLine CE)) :
    formParallelogram c d l h AB KM CE DG := by
  euclid_intros
  have hdh : d ≠ h := fun heq => hhoffAB (heq ▸ hdAB)
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hx; euclid_apply (intersection_symm AB KM); euclid_finish
  have hCEDG : ¬(CE.intersectsLine DG) := by
    intro hx; euclid_apply (intersection_symm CE DG); euclid_finish
  exact ⟨hcAB, hdAB, hlKM, hhKM, hcCE, hlCE, ⟨hdDG, hhDG, hdh⟩, hsscl, hABKM, hCEDG⟩

end Elements.Book2
