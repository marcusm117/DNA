import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: h ∉ DE. h and d both lie on AD, with d ∈ AD ∩ DE. If h ∈ DE then h, d are two common
   points of AD and DE; with h ≠ d this forces AD = DE, putting a (∈ AD) on DE — but a ∉ DE. -/
theorem helper_2_7_step3_hnde (a b d g h : Point) (AB AD HF BD DE : Line)
    (haAB : a.onLine AB)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (hdDE : d.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHF : g.onLine HF) (hhHF : h.onLine HF)
    (hDEAB : ¬(DE.intersectsLine AB))
    (step3_dnab : ¬(d.onLine AB))
    (step3_bgd : between b g d)
    (step3_bnhf : ¬(b.onLine HF)) :
    ¬(h.onLine DE) := by
  intro hhDE
  have hDEneAB : DE ≠ AB := fun hh => step3_dnab (hh ▸ hdDE)
  have hanDE : ¬(a.onLine DE) := by
    intro haDE
    euclid_apply (intersection_lines_common_point a DE AB)
    euclid_finish
  have hgd : g ≠ d := by euclid_finish
  have hdnhf : ¬(d.onLine HF) := by
    intro hdHF
    have hHFBD : HF = BD := by
      euclid_apply (two_points_determine_line g d HF BD)
      euclid_finish
    exact step3_bnhf (hHFBD.symm ▸ hbBD)
  have hhd : h ≠ d := fun hh => hdnhf (hh ▸ hhHF)
  euclid_apply (two_points_determine_line h d AD DE)
  euclid_finish

end Elements.Book2
