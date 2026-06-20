import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.16: the rectangle by AD and DB, plus the square on CB, is equal to the square on CD. From
   step14 (AD·DB + CB² = gnomon + LG) and step15 (gnomon + LG = △c:e:f + △c:f:d = CD²), by
   transitivity. Pure area-arithmetic over the two prior step equalities. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step16 (a b c d m l h f g e : Point)
    (hstep14 : |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| =
      ((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e))
    (hstep15 : (((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e) =
        Triangle.area △ c:e:f + Triangle.area △ c:f:d) ∧
      (Triangle.area △ c:e:f + Triangle.area △ c:f:d = |(c─d)| * |(c─d)|)) :
    |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| := by
  euclid_finish

end Elements.Book2
