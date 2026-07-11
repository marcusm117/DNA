import SystemE
import Book3.Prop20.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_21_step4
    (a b d e f' : Point) (BD : Line) (ABCD : Circle)
    (h_f'_centre : f'.isCentre ABCD)
    (h_e_circ : e.onCircle ABCD)
    (h_bdc : b.onCircle ABCD ∧ d.onCircle ABCD ∧ distinctPointsOnLine b d BD)
    (h_aSe : a.sameSide e BD)
    (h_major : a.sameSide f' BD) :
    ∠ b:f':d = ∠ b:e:d + ∠ b:e:d := by
  euclid_apply (proposition_20 e b d f' BD ABCD)
  euclid_finish

end Elements.Book3
