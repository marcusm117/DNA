import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(b.onLine EF). b ∈ AB; EF ∥ AB (hEFAB). EF ≠ AB because e ∈ EF is off AB
   (step8_eoffab). A common point b would then force EF, AB to meet. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_boffef (b e : Point) (AB EF : Line)
    (hbAB : b.onLine AB) (heEF : e.onLine EF)
    (heoffAB : ¬(e.onLine AB))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(b.onLine EF) := by
  intro hbEF
  have hEFneAB : EF ≠ AB := fun heq => heoffAB (heq ▸ heEF)
  euclid_apply (intersection_lines_common_point b EF AB)
  euclid_finish

end Elements.Book2
