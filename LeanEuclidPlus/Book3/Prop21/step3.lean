import SystemE
import Book3.Prop20.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_21_step3
    (a b d e f' : Point) (BD : Line) (ABCD : Circle)
    (hassump1 : f'.isCentre ABCD)
    (hassump2 : a.onCircle ABCD)
    (hassump3 : b.onCircle ABCD ∧ d.onCircle ABCD ∧ distinctPointsOnLine b d BD)
    (he : e.onCircle ABCD) (hss : a.sameSide e BD)
    (h_major : a.sameSide f' BD) :
    ∠ b:f':d = ∠ b:a:d + ∠ b:a:d := by
  euclid_apply (proposition_20 a b d f' BD ABCD)
  euclid_finish

end Elements.Book3
