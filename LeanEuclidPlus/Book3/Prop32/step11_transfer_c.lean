import SystemE
import Book3.Prop21.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- III.21 transfer (obtuse): `c` and the antipode `a'` are in the same segment DCB (both opposite `e`
-- across BD), so ∠b:c:d = ∠b:a':d.
theorem helper_3_32_step11_transfer_c (c a' b d e : Point) (ABCD : Circle) (BD : Line)
    (h_c_circ : c.onCircle ABCD) (h_b_circ : b.onCircle ABCD) (h_d_circ : d.onCircle ABCD)
    (h_a'_circ : a'.onCircle ABCD)
    (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD) (h_bd : b ≠ d)
    (h_c_offBD : ¬c.onLine BD) (h_a'_offBD : ¬a'.onLine BD) (h_e_offBD : ¬e.onLine BD)
    (h_ce_opp : ¬c.sameSide e BD) (h_a'e_opp : ¬a'.sameSide e BD) :
    ∠ b:c:d = ∠ b:a':d := by
  have h_same : c.sameSide a' BD := by euclid_finish
  euclid_apply (Elements.Book3.proposition_21 c b d a' BD ABCD)
  euclid_finish

end Elements.Book3
