import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6 / step6_chpar: h ≠ b. h is on KM (the middle parallel), b is on AB (the top
   line). KM ≠ AB because h ∈ KM but h ∉ AB (step6_hoffab); with KM ∦ AB, a shared point h = b would
   force KM, AB to meet. -/
theorem helper_2_6_step6_hb (b h : Point) (AB KM : Line)
    (hhKM : h.onLine KM) (hbAB : b.onLine AB)
    (hhoffAB : ¬(h.onLine AB))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    h ≠ b := by
  have hKMneAB : KM ≠ AB := fun hh => hhoffAB (hh ▸ hhKM)
  intro hhb
  rw [hhb] at hhKM
  euclid_apply (intersection_lines_common_point b KM AB)
  euclid_finish

end Elements.Book2
