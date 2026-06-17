import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(h.onLine AB). h ∈ BE with between b h e; b ∈ AB; e ∉ AB (step8_eoffab).
   If h ∈ AB then b,h ∈ AB ∩ BE with b ≠ h (between b h e ⟹ b ≠ h), so AB = BE, hence
   e ∈ AB — contradicting e ∉ AB. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_hoffab (b e h : Point) (AB BE : Line)
    (hbAB : b.onLine AB) (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hbhe : between b h e)
    (heoffAB : ¬(e.onLine AB)) :
    ¬(h.onLine AB) := by
  intro hhAB
  have hbh : b ≠ h := by euclid_finish
  have hABisBE : AB = BE := by
    euclid_apply (two_points_determine_line b h AB BE)
    euclid_finish
  exact heoffAB (hABisBE ▸ heBE)

end Elements.Book2
