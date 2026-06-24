import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step9 (g c b k d n q r p : Point)
    (h_step6 : Triangle.area △ g:c:b + Triangle.area △ g:b:k =
      Triangle.area △ k:b:d + Triangle.area △ k:d:n)
    (h_step7 : Triangle.area △ g:k:r + Triangle.area △ g:r:q =
      Triangle.area △ k:n:p + Triangle.area △ k:p:r)
    (h_step8 : Triangle.area △ g:c:b + Triangle.area △ g:b:k =
      Triangle.area △ k:n:p + Triangle.area △ k:p:r) :
    Triangle.area △ k:b:d + Triangle.area △ k:d:n =
      Triangle.area △ g:k:r + Triangle.area △ g:r:q := by
  euclid_finish

end Elements.Book2
