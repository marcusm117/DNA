import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.10: the rectangle A·BC equals A·BD + A·DE + A·EC. Pure linear arithmetic: step5 says the big
   rectangle's area = the three sub-rectangles' areas; step6 ties the big area to |A|·|BC|, and
   step7,8,9 tie each sub-area to |A|·|BD|, |A|·|DE|, |A|·|EC|. Chaining gives the conclusion. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step10 (a₁ a₂ b c d e g h k l : Point)
    (step5 : Triangle.area △ b:c:h + Triangle.area △ b:g:h =
      (Triangle.area △ b:d:k + Triangle.area △ b:g:k)
    + (Triangle.area △ d:e:l + Triangle.area △ d:k:l)
    + (Triangle.area △ e:c:h + Triangle.area △ e:l:h))
    (step6 : Triangle.area △ b:c:h + Triangle.area △ b:g:h = |(a₁─a₂)| * |(b─c)|)
    (step7 : Triangle.area △ b:d:k + Triangle.area △ b:g:k = |(a₁─a₂)| * |(b─d)|)
    (step8 : Triangle.area △ d:e:l + Triangle.area △ d:k:l = |(a₁─a₂)| * |(d─e)|)
    (step9 : Triangle.area △ e:c:h + Triangle.area △ e:l:h = |(a₁─a₂)| * |(e─c)|) :
    |(a₁─a₂)| * |(b─c)| = |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)| := by
  euclid_finish

end Elements.Book2
