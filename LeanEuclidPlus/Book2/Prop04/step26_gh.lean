import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.26 sub: g ≠ h. h lies on AD, which is parallel to CF (¬CF.intersectsLine AD) and distinct from
   it (c ∈ CF, c ∉ AD); so h ∉ CF. But g ∈ CF, hence g ≠ h. -/
theorem helper_2_4_step26_gh (g h c : Point) (CF AD : Line)
    (hgCF : g.onLine CF) (hhAD : h.onLine AD)
    (hADCF : AD ≠ CF) (hCFAD : ¬(CF.intersectsLine AD)) :
    g ≠ h := by
  have hhnCF : ¬(h.onLine CF) := by
    intro hhCF; euclid_apply (intersection_lines_common_point h CF AD); euclid_finish
  intro hgh
  rw [hgh] at hgCF
  exact hhnCF hgCF

end Elements.Book2
