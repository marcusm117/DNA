import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.12 sub-sub: d.sameSide h AK. d,h both on DG, and AK ∥ DG (¬AK∩DG, AK ≠ DG since d ∉ AK),
   so they cannot be on opposite sides of AK (intersection_lines_opposing would force AK∩DG). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step12_sshc_dh (a d h : Point) (AB AK DG : Line)
    (haAB : a.onLine AB) (hdAB : d.onLine AB)
    (haAK : a.onLine AK)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (had : a ≠ d)
    (hAKAB : AK ≠ AB)
    (hAKDG : ¬(AK.intersectsLine DG)) :
    d.sameSide h AK := by
  euclid_intros
  -- d ∉ AK: if d ∈ AK then a,d ∈ AK ∩ AB with a ≠ d ⟹ AK = AB, contra hAKAB
  have hdoffAK : ¬(d.onLine AK) := by
    intro hon
    have hAKeqAB : AK = AB := by
      euclid_apply (two_points_determine_line a d AK AB)
      euclid_finish
    exact hAKAB hAKeqAB
  have hAKDGne : AK ≠ DG := fun heq => hdoffAK (by rw [heq]; exact hdDG)
  -- h ∉ AK: h ∈ DG, AK ∥ DG (AK ≠ DG just shown)
  have hhoffAK : ¬(h.onLine AK) := by
    intro hon; euclid_apply (intersection_lines_common_point h AK DG); euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing d h AK DG)
  euclid_finish

end Elements.Book2
