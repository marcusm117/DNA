import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(c.onLine KM). c ∈ AB; KM ∥ AB (hKMAB). KM ≠ AB because h ∈ KM is off AB
   (step8_hoffab). A common point c would then force KM, AB to meet. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_coffkm (c h : Point) (AB KM : Line)
    (hcAB : c.onLine AB) (hhKM : h.onLine KM)
    (hhoffAB : ¬(h.onLine AB))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    ¬(c.onLine KM) := by
  intro hcKM
  have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
  euclid_apply (intersection_lines_common_point c KM AB)
  euclid_finish

end Elements.Book2
