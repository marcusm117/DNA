import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.26 final: from area(ACGH) = |a─c|·|a─h| (step26_area), |a─h| = |c─g| (step22_acgh) and
   |b─c| = |c─g| (step8), conclude △a:c:g + △a:g:h = |a─c|·|c─b| (area + distance symmetry). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step26_close (a b c g h : Point)
    (harea : Triangle.area △ a:h:g + Triangle.area △ a:g:c = |(a─c)| * |(a─h)|)
    (hahcg : |(a─h)| = |(c─g)|) (hstep8 : |(b─c)| = |(c─g)|) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)| := by
  euclid_finish

end Elements.Book2
