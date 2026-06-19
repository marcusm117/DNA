import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_body (b d f g : Point) (AB BF DG EF : Line)
    (hdDG : d.onLine DG) (hgDG : g.onLine DG)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hgEF : g.onLine EF) (hfEF : f.onLine EF)
    (hgf : g ≠ f)
    (hss : d.sameSide b EF)
    (hDGBF : ¬(DG.intersectsLine BF))
    (habef : ¬(AB.intersectsLine EF)) :
    formParallelogram d g b f DG BF AB EF :=
  ⟨hdDG, hgDG, hbBF, hfBF, hdAB, hbAB, ⟨hgEF, hfEF, hgf⟩, hss, hDGBF, habef⟩

end Elements.Book2
