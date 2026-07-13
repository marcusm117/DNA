import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- ∠b:a:d = ∠a:e:b : both are right angles — ∠b:a:d = ∟ (angle at A = C = ∟) and the angle ∠a:e:b in
-- the semicircle is also ∟ (assumption gap, Prop 3.31).
theorem helper_3_33_step23
    (a b d e : Point)
    (hbad : ∠ b:a:d = ∟)
    (hassump1 : ∠ a:e:b = ∟)   -- "(the latter angle), being in a semi-circle, is also a right-angle"
    : ∠ b:a:d = ∠ a:e:b := by
  euclid_finish

end Elements.Book3
