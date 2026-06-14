import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.9 (length): e ≠ l. e is on BC, l is on GH, GH ∦ BC and GH ≠ BC (g on GH is off
   BC), so a common point would force GH and BC to intersect. Hence e ≠ l. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step9_len_neq (e g l : Point) (BC GH : Line)
    (heBC : e.onLine BC) (hgGH : g.onLine GH) (hgoffBC : ¬(g.onLine BC)) (hlGH : l.onLine GH)
    (hGHBC : ¬(GH.intersectsLine BC)) :
    e ≠ l := by
  euclid_intros
  have hGHneBC : GH ≠ BC := by euclid_finish
  by_contra heql
  euclid_apply (intersection_lines_common_point e GH BC)
  euclid_finish

end Elements.Book2
