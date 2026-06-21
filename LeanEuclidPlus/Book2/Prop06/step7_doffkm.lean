import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: d ∉ KM. d ∈ AB, KM ∥ AB (¬KM.intersectsLine AB) and KM ≠ AB (h ∈ KM, ¬h ∈ AB). A point
   on AB cannot lie on the parallel KM. -/
theorem helper_2_6_step7_doffkm (d h : Point) (AB KM : Line)
    (hdAB : d.onLine AB) (hhKM : h.onLine KM)
    (hhoffAB : ¬(h.onLine AB))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    ¬(d.onLine KM) := by
  intro hdKM
  have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
  euclid_apply (intersection_lines_common_point d KM AB)
  euclid_finish

end Elements.Book2
