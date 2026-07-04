import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_21_step8 (a b c d e : Point)
    (hstep4 : |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)|)
    (hstep6 : |(c─e)| + |(e─b)| > |(c─d)| + |(d─b)|) :
    |(b─a)| + |(a─c)| > |(b─d)| + |(d─c)| := by
  have hec_sym : |(e─c)| = |(c─e)| := segment_symmetric e c
  have hbe_sym : |(b─e)| = |(e─b)| := segment_symmetric b e
  have hbd_sym : |(b─d)| = |(d─b)| := segment_symmetric b d
  have hdc_sym : |(d─c)| = |(c─d)| := segment_symmetric d c
  linarith

end Elements.Book1
