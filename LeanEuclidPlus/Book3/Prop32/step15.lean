import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_32_step15 (a b c d e f : Point) (BD : Line)
    (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD) (h_c_offBD : ¬c.onLine BD)
    (step11 : ∠ f:b:d = ∠ b:a:d)
    (step14 : ∠ f:b:d + ∠ e:b:d = ∠ b:a:d + ∠ b:c:d) :
    ∠ e:b:d = ∠ d:c:b := by
  euclid_apply (angle_symm b c d)
  euclid_finish

end Elements.Book3
