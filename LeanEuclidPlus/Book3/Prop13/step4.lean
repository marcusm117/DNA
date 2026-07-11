import SystemE
import Book3.Prop11.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_13_step4 (ABDC EBFD : Circle) (d b g h : Point) (GH : Line)
    (hd_ABDC : d.onCircle ABDC) (hd_EBFD : d.onCircle EBFD)
    (hb_ABDC : b.onCircle ABDC) (hb_EBFD : b.onCircle EBFD)
    (hne : ABDC ≠ EBFD)
    (hnint : ¬ABDC.intersectsCircle EBFD)
    (hins : h.insideCircle ABDC)
    (hcenABDC : g.isCentre ABDC) (hcenEBFD : h.isCentre EBFD)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) :
    d.onLine GH ∧ b.onLine GH := by
  have hgh : g ≠ h := by
    intro heq
    subst heq
    have : ABDC = EBFD := by euclid_finish
    exact hne this
  have hbet_d : between g h d := by
    euclid_apply (proposition_11 d g h ABDC EBFD)
    assumption
  have hbet_b : between g h b := by
    euclid_apply (proposition_11 b g h ABDC EBFD)
    assumption
  constructor
  · euclid_apply (between_same_line_out g h d GH)
    assumption
  · euclid_apply (between_same_line_out g h b GH)
    assumption

end Elements.Book3
