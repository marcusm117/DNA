import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- CD is a diameter (e between c and d): |CD| = |CE| + |ED| = 2R = 2·|AE|.
theorem helper_3_14_hdiam_cd
    (a c d e : Point) (ABDC : Circle)
    (ha : a.onCircle ABDC) (hc : c.onCircle ABDC) (hd : d.onCircle ABDC)
    (hcen : e.isCentre ABDC) (hbet : between c e d) :
    |(c─d)| = |(a─e)| + |(a─e)| := by
  have hsum : |(c─e)| + |(e─d)| = |(c─d)| := between_if c e d hbet
  have hrad_ce : |(c─e)| = |(a─e)| := by euclid_finish
  have hrad_ed : |(e─d)| = |(a─e)| := by euclid_finish
  linarith

end Elements.Book3
