import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.12: gnomon NOP = |(a─d)| * |(d─b)|. From step10 (whole AM = gnomon) and step11
   (AM = |a─d|·|d─b|), by transitivity. Pure area-arithmetic over the two prior step equalities. -/
theorem helper_2_6_step12 (a b d m k c l h f g : Point)
    (hstep10 : Triangle.area △ a:d:m + Triangle.area △ a:m:k =
      (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g))
    (hstep11 : Triangle.area △ a:d:m + Triangle.area △ a:m:k = |(a─d)| * |(d─b)|) :
    (Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
      (Triangle.area △ h:m:f + Triangle.area △ h:f:g) = |(a─d)| * |(d─b)| := by
  euclid_finish

end Elements.Book2
