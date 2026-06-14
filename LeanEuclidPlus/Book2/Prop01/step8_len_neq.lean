import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.8 (length): d ≠ k. d is on BC, k is on GH, GH ∦ BC and GH ≠ BC (g on GH is off
   BC), so a common point would force GH and BC to intersect. Hence d ≠ k. -/
theorem helper_2_1_step8_len_neq (d g k : Point) (BC GH : Line)
    (hdBC : d.onLine BC) (hgGH : g.onLine GH) (hgoffBC : ¬(g.onLine BC)) (hkGH : k.onLine GH)
    (hGHBC : ¬(GH.intersectsLine BC)) :
    d ≠ k := by
  euclid_intros
  have hGHneBC : GH ≠ BC := by euclid_finish
  by_contra hdqk
  euclid_apply (intersection_lines_common_point d GH BC)
  euclid_finish

end Elements.Book2
