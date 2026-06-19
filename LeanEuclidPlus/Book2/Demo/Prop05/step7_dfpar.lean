import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.7 sub: formParallelogram d g b f DG BF AB EF (rectangle DF).
   def p1 p2 p3 p4 L1 L2 L3 L4: p1=d,p2=g on L1=DG; p3=b,p4=f on L2=BF;
   p1=d,p3=b on L3=AB; p2=g,p4=f on L4=EF; p1.sameSide p3 L4 = d.sameSide b EF;
   ¬(DG∥BF), ¬(AB∥EF).
   g ≠ f: g on DG, f on BF; DG ∥ BF so g ≠ f (or g off BF and g on DG). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar (b d f g : Point) (AB BF DG EF : Line)
    (hdDG : d.onLine DG) (hgDG : g.onLine DG)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hgEF : g.onLine EF) (hfEF : f.onLine EF)
    (hgoffBF : ¬(g.onLine BF))
    (hdssb_EF : d.sameSide b EF)
    (hDGBF : ¬(DG.intersectsLine BF))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    formParallelogram d g b f DG BF AB EF := by
  euclid_intros
  have hgf : g ≠ f := by euclid_finish
  have hDGBF' : ¬(DG.intersectsLine BF) := hDGBF
  have hABEF : ¬(AB.intersectsLine EF) := by
    intro hx; euclid_apply (intersection_symm AB EF); euclid_finish
  exact ⟨hdDG, hgDG, hbBF, hfBF, hdAB, hbAB, ⟨hgEF, hfEF, hgf⟩, hdssb_EF, hDGBF', hABEF⟩

end Elements.Book2
