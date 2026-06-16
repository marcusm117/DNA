import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.13: |DH| = |DB|. Since KM ∥ AB and D,B on AB and H on KM, DH and DB are
   opposite sides of parallelogram, hence equal. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step13 (d b h : Point) (AB KM DG : Line)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hhKM : h.onLine KM) (hhDG : h.onLine DG) (hdDG : d.onLine DG)
    (hKMAB : ¬(KM.intersectsLine AB)) :
    |(d─h)| = |(d─b)| := by
  euclid_finish

end Elements.Book2