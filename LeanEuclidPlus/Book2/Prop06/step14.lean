import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.14: |(a─d)|·|(d─b)| + |(c─b)|·|(c─b)| = gnomon NOP + (square) LG. From step12
   (gnomon = |a─d|·|d─b|) and step13 (LG = |c─b|·|c─b|), by adding. Pure area-arithmetic. -/
theorem helper_2_6_step14 (a b c d m l h f g e : Point)
    (hstep12 : (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g) = |(a─d)| * |(d─b)|)
    (hstep13 : Triangle.area △ l:h:g + Triangle.area △ l:g:e = |(c─b)| * |(c─b)|) :
    |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| =
      ((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e) := by
  euclid_finish

end Elements.Book2
