import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step11 (g c b k d n q r p : Point)
    (h_step10 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k =
        Triangle.area △ k:b:d + Triangle.area △ k:d:n) ∧
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n =
        Triangle.area △ g:k:r + Triangle.area △ g:r:q) ∧
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q =
        Triangle.area △ k:n:p + Triangle.area △ k:p:r)) :
    (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) =
      4 * (Triangle.area △ g:c:b + Triangle.area △ g:b:k) := by
  rcases h_step10 with ⟨h1, h2, h3⟩
  linarith

end Elements.Book2
