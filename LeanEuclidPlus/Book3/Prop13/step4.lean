import SystemE
import Book3.Prop11.Main
import Book3.Prop13.step4_int
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_13_step4 (ABDC EBFD : Circle) (d b g h : Point) (GH : Line)
    (hd_ABDC : d.onCircle ABDC) (hd_EBFD : d.onCircle EBFD)
    (hb_ABDC : b.onCircle ABDC) (hb_EBFD : b.onCircle EBFD)
    (hdb : d ≠ b)
    (hne : ABDC ≠ EBFD)
    (hnint : ¬ABDC.intersectsCircle EBFD)
    (hins : h.insideCircle ABDC)
    (hcenABDC : g.isCentre ABDC) (hcenEBFD : h.isCentre EBFD)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) :
    d.onLine GH ∧ b.onLine GH := by
  have hgh : g ≠ h := by
    intro heq
    subst heq
    exact hne (by euclid_finish)
  -- The two distinct common points d, b force the circles to intersect — impossible (hnint). This
  -- inconsistency discharges III.11's inner-circle precondition |h·|<|g·| at each contact.
  have step4_int : ABDC.intersectsCircle EBFD := by euclid_apply (helper_3_13_step4_int ABDC EBFD d b g h GH (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle EBFD; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle EBFD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show ABDC ≠ EBFD; assumption)) (by euclid_assumption "" (show g.isCentre ABDC; assumption)) (by euclid_assumption "" (show h.isCentre EBFD; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)))
  have hrad_d : |(h─d)| < |(g─d)| := absurd step4_int hnint
  have hrad_b : |(h─b)| < |(g─b)| := absurd step4_int hnint
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
