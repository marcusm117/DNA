import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step8 (b d e : Point) (BCD : Circle)
    (hcen : e.isCentre BCD)
    (hd : d.onCircle BCD)
    (hb : b.onCircle BCD) :
    |(e─d)| = |(e─b)| := by
  have h := point_on_circle_onlyif e d b BCD ⟨hcen, hd, hb⟩
  linarith [segment_symmetric e d, segment_symmetric e b]

end Elements.Book3
