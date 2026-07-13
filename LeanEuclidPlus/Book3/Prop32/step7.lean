import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_32_step7 (a' b d : Point) (ABCD : Circle) (BA BD AD : Line)
    (h_a'_circ : a'.onCircle ABCD) (h_b_circ : b.onCircle ABCD) (h_d_circ : d.onCircle ABCD)
    (h_a'_BA : a'.onLine BA) (h_b_BA : b.onLine BA)
    (h_d_BD : d.onLine BD) (h_b_BD : b.onLine BD) (h_bd : b ≠ d) (h_da' : d ≠ a')
    (h_a'_AD : a'.onLine AD) (h_d_AD : d.onLine AD)
    (step6 : ∠ a':d:b = ∟) :
    ∠ b:a':d + ∠ a':b:d = ∟ := by
  have h_d_offBA : ¬d.onLine BA := by euclid_finish
  euclid_apply (extend_point BA a' b) as k
  euclid_apply (Elements.Book1.proposition_32 d a' b k AD BA BD)
  euclid_finish

end Elements.Book3
