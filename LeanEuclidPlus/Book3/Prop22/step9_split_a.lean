import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step9_split_a (a b c d : Point) (AC BD : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
  (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hbd : b ≠ d)
  (hbAC : ¬b.onLine AC) (hdAC : ¬d.onLine AC) (hbd_opp : ¬b.sameSide d AC)
  (haBD : ¬a.onLine BD) (hcBD : ¬c.onLine BD) (hac_opp : ¬a.sameSide c BD)
  : ∠ d:a:b = ∠ d:a:c + ∠ c:a:b := by
  euclid_apply (intersection_lines_opposing a c BD AC)
  euclid_apply (intersection_lines BD AC) as x
  have hax : a ≠ x := by euclid_finish
  have hcx : c ≠ x := by euclid_finish
  have hbx : b ≠ x := by euclid_finish
  have hdx : d ≠ x := by euclid_finish
  euclid_apply (pasch_4 a x c BD AC)
  euclid_apply (pasch_4 b x d AC BD)
  have hab : a ≠ b := by euclid_finish
  have had : a ≠ d := by euclid_finish
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points a d) as AD
  have hdc_AB : d.sameSide c AB := by euclid_finish
  have hbc_AD : b.sameSide c AD := by euclid_finish
  euclid_apply (sum_angles_onlyif a d b c AD AB)
  euclid_finish

end Elements.Book3
