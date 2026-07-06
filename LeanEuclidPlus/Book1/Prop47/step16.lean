import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- BL = 2·△ABD (step13), GB = 2·△FBC (step14), 2·△ABD = 2·△FBC (step15 applied to step12) ⟹ BL = GB.
theorem helper_1_47_step16
    (a b c d f g m l : Point)
    (h13 : Triangle.area △ b:m:l + Triangle.area △ b:l:d = Triangle.area △ a:b:d + Triangle.area △ a:b:d)
    (h14 : Triangle.area △ a:g:f + Triangle.area △ a:f:b = Triangle.area △ f:b:c + Triangle.area △ f:b:c)
    (h15 : Triangle.area △ a:b:d = Triangle.area △ f:b:c →
      Triangle.area △ a:b:d + Triangle.area △ a:b:d = Triangle.area △ f:b:c + Triangle.area △ f:b:c)
    (h12 : Triangle.area △ a:b:d = Triangle.area △ f:b:c) :
    Triangle.area △ b:m:l + Triangle.area △ b:l:d = Triangle.area △ a:g:f + Triangle.area △ a:f:b := by
  have hdoubles := h15 h12
  euclid_finish

end Elements.Book1
