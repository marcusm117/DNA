import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_hd_ex (f g h : Point) (ADE : Circle)
    (left_5 : g.isCentre ADE)
    (h_bet_fgh : between f g h)
    (h_out : h.outsideCircle ADE)
    : ∃ d : Point, d.onCircle ADE ∧ between g d h := by
  -- Save components before euclid_apply destructs the outsideCircle conjunction
  have h_not_in : ¬h.insideCircle ADE := h_out.1
  have h_not_on : ¬h.onCircle ADE := h_out.2
  euclid_apply (line_from_points f g) as FG
  have hg_on_FG : g.onLine FG := by euclid_finish
  have hf_on_FG : f.onLine FG := by euclid_finish
  have hh_on_FG : h.onLine FG :=
    between_same_line_out f g h FG ⟨h_bet_fgh, hf_on_FG, hg_on_FG⟩
  have hg_in_ADE : g.insideCircle ADE := center_inside_circle g ADE left_5
  have h_out_r : h.outsideCircle ADE := ⟨h_not_in, h_not_on⟩
  obtain ⟨d, hd_ADE, _, hd_bet⟩ :=
    intersection_circle_line_between_points ADE FG g h ⟨hg_in_ADE, hg_on_FG, h_out_r, hh_on_FG⟩
  exact ⟨d, hd_ADE, hd_bet⟩

end Elements.Book3
