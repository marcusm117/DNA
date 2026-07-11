import SystemE
import Book3.Prop21.step5_minor_arc_a
import Book3.Prop21.step5_minor_arc_e
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_21_step5_minor
    (a b d e f' : Point) (BD BF FD : Line) (ABCD : Circle)
    (h_f'_centre : f'.isCentre ABCD)
    (h_a_circ : a.onCircle ABCD)
    (h_e_circ : e.onCircle ABCD)
    (h_bdc : b.onCircle ABCD ∧ d.onCircle ABCD ∧ distinctPointsOnLine b d BD)
    (h_bBF : b.onLine BF) (h_f'BF : f'.onLine BF)
    (h_f'FD : f'.onLine FD) (h_dFD : d.onLine FD)
    (h_aSe : a.sameSide e BD)
    (h_major : ¬a.sameSide f' BD) :
    ∠ b:a:d = ∠ b:e:d := by
  obtain ⟨h_b_circ, h_d_circ, h_bd⟩ := h_bdc
  have h_a_off : ¬ a.onLine BD := by euclid_finish
  have h_e_off : ¬ e.onLine BD := by euclid_finish
  have h_e_major : ¬ e.sameSide f' BD := by euclid_finish
  have step5_minor_arc_a : ∠ b:a:d + ∠ b:a:d + ∠ b:f':d = ∟ + ∟ + ∟ + ∟ := by euclid_apply (helper_3_21_step5_minor_arc_a a b d f' BD ABCD (by euclid_assumption "" (show f'.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show distinctPointsOnLine b d BD; assumption)) (by euclid_assumption "" (show ¬ a.onLine BD; assumption)) (by euclid_assumption "" (show ¬ a.sameSide f' BD; assumption)))
  have step5_minor_arc_e : ∠ b:e:d + ∠ b:e:d + ∠ b:f':d = ∟ + ∟ + ∟ + ∟ := by euclid_apply (helper_3_21_step5_minor_arc_e e b d f' BD ABCD (by euclid_assumption "" (show f'.isCentre ABCD; assumption)) (by euclid_assumption "" (show e.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show distinctPointsOnLine b d BD; assumption)) (by euclid_assumption "" (show ¬ e.onLine BD; assumption)) (by euclid_assumption "" (show ¬ e.sameSide f' BD; assumption)))
  euclid_finish

end Elements.Book3
