import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step17 (a c g m o q r l h p f : Point)
    (h_step13 : Triangle.area △ a:c:g + Triangle.area △ a:g:m =
      Triangle.area △ m:g:q + Triangle.area △ m:q:o)
    (h_step15 : Triangle.area △ m:g:q + Triangle.area △ m:q:o =
      Triangle.area △ q:r:l + Triangle.area △ q:l:h)
    (h_step14 : Triangle.area △ q:r:l + Triangle.area △ q:l:h =
      Triangle.area △ r:p:f + Triangle.area △ r:f:l) :
    (Triangle.area △ a:c:g + Triangle.area △ a:g:m =
        Triangle.area △ m:g:q + Triangle.area △ m:q:o) ∧
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o =
        Triangle.area △ q:r:l + Triangle.area △ q:l:h) ∧
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h =
        Triangle.area △ r:p:f + Triangle.area △ r:f:l) := by
  euclid_finish

end Elements.Book2
