import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6 / step6_alpar: l ≠ c. l is on KM (the middle parallel), c is on AB (the top
   line). KM ≠ AB because h ∈ KM but h ∉ AB; with KM ∦ AB, a shared point l = c forces KM, AB to meet.
   h ∉ AB is supplied (step6_hoffab). -/
theorem helper_2_6_step6_lc (c l h : Point) (AB KM : Line)
    (hlKM : l.onLine KM) (hcAB : c.onLine AB)
    (hhKM : h.onLine KM) (hhoffAB : ¬(h.onLine AB))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    l ≠ c := by
  have hKMneAB : KM ≠ AB := fun hh => hhoffAB (hh ▸ hhKM)
  intro hlc
  rw [hlc] at hlKM
  euclid_apply (intersection_lines_common_point c KM AB)
  euclid_finish

end Elements.Book2
