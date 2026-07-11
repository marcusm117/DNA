import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step5 (a b c d : Point) (AC BD : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
  (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hbd : b ≠ d)
  (hbAC : ¬b.onLine AC) (hdAC : ¬d.onLine AC) (hbd_opp : ¬b.sameSide d AC)
  (haBD : ¬a.onLine BD) (hcBD : ¬c.onLine BD) (hac_opp : ¬a.sameSide c BD)
  (hstep3 : ∠ c:a:b = ∠ b:d:c) (hstep4 : ∠ a:c:b = ∠ a:d:b)
  : ∠ a:d:c = ∠ b:a:c + ∠ a:c:b := by
  euclid_apply (intersection_lines_opposing a c BD AC)
  euclid_apply (intersection_lines BD AC) as x
  have hax : a ≠ x := by euclid_finish
  have hcx : c ≠ x := by euclid_finish
  have hbx : b ≠ x := by euclid_finish
  have hdx : d ≠ x := by euclid_finish
  euclid_apply (pasch_4 a x c BD AC)
  euclid_apply (pasch_4 b x d AC BD)
  have hda : d ≠ a := by euclid_finish
  have hdc : d ≠ c := by euclid_finish
  euclid_apply (line_from_points d a) as DA
  euclid_apply (line_from_points d c) as DC
  have hab_DC : a.sameSide b DC := by euclid_finish
  have hcb_DA : c.sameSide b DA := by euclid_finish
  euclid_apply (sum_angles_onlyif d a c b DA DC)
  euclid_finish

end Elements.Book3
