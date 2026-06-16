import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub: d ≠ h. d ∈ AB; h ∈ KM; AB ∥ KM → d ∉ KM → d ≠ h. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11_ahpar_dh (d h k : Point) (AB KM : Line)
    (hdAB : d.onLine AB) (hhKM : h.onLine KM) (hkKM : k.onLine KM) (hkAB : k.onLine AB)
    (hKMAB : ¬(KM.intersectsLine AB)) :
    d ≠ h := by
  intro heq
  have hKMneAB : KM ≠ AB := by
    intro heq2
    exact hKMAB (by rw [heq2]; euclid_finish)
  have hdKM : d.onLine KM := heq ▸ hhKM
  euclid_apply (intersection_lines_common_point d KM AB)
  euclid_finish

end Elements.Book2
