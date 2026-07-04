import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_21_step6 (b c d e : Point)
    (hstep1 : between b d e ∧ e.onLine BD)
    (hstep5 : |(c─e)| + |(e─d)| + |(d─b)| > |(c─d)| + |(d─b)|) :
    |(c─e)| + |(e─b)| > |(c─d)| + |(d─b)| := by
  have hbet : between b d e := hstep1.1
  have hbd_eq : |(b─d)| + |(d─e)| = |(b─e)| := between_if b d e hbet
  have hed_sym : |(e─d)| = |(d─e)| := segment_symmetric e d
  have heb_sym : |(e─b)| = |(b─e)| := segment_symmetric e b
  have hdb_sym : |(d─b)| = |(b─d)| := segment_symmetric d b
  linarith

end Elements.Book1
