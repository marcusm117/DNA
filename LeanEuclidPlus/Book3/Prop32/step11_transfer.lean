import SystemE
import Book3.Prop21.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- III.21 transfer (acute): `a` and the antipode `a'` are in the same segment BAD (both opposite `f`
-- across BD), so the inscribed angles are equal: ∠b:a:d = ∠b:a':d.
theorem helper_3_32_step11_transfer (a a' b d f : Point) (ABCD : Circle) (BD : Line)
    (h_a_circ : a.onCircle ABCD) (h_b_circ : b.onCircle ABCD) (h_d_circ : d.onCircle ABCD)
    (h_a'_circ : a'.onCircle ABCD)
    (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD) (h_bd : b ≠ d)
    (h_a_offBD : ¬a.onLine BD) (h_a'_offBD : ¬a'.onLine BD) (h_f_offBD : ¬f.onLine BD)
    (h_af_opp : ¬a.sameSide f BD) (h_a'f_opp : ¬a'.sameSide f BD) :
    ∠ b:a:d = ∠ b:a':d := by
  have h_same : a.sameSide a' BD := by euclid_finish
  euclid_apply (Elements.Book3.proposition_21 a b d a' BD ABCD)
  euclid_finish

end Elements.Book3
