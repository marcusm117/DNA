import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_gapDiam_powac_diam (a c e f : Point) (ABCD : Circle) (AC : Line)
  (ha : a.onCircle ABCD) (hc : c.onCircle ABCD) (hbet1 : between a e c)
  (hfc : f.isCentre ABCD) (haAC : a.onLine AC) (hcAC : c.onLine AC)
  (hf_ac : f.onLine AC)
  : |(a─e)| * |(e─c)| + |(f─e)| * |(f─e)| = |(f─a)| * |(f─a)| := by
  euclid_finish

end Elements.Book3
