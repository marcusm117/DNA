import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step22 (a b c d e f g k n m o q r l h p : Point)
    (h_step20 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) =
      4 * (Triangle.area △ a:b:k + Triangle.area △ a:k:m)) :
    (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) =
      4 * (Triangle.area △ a:b:k + Triangle.area △ a:k:m) := by
  exact h_step20

end Elements.Book2
