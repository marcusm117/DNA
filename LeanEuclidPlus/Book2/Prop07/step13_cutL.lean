import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: cut the left half ADNC by the horizontal HF into AG (ACGH) and DG (HGND).
   sum_parallelograms_area on formParallelogram a d c n AD CN AB DE, cut a-h-d (on AD) and c-g-n
   (on CN). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_cutL (a d c n h g : Point) (AD CN AB DE : Line)
    (hpar : formParallelogram a d c n AD CN AB DE)
    (hahd : between a h d) (hcgn : between c g n) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h
      + (Triangle.area △ h:g:n + Triangle.area △ h:n:d)
      = Triangle.area △ a:c:n + Triangle.area △ a:n:d := by
  euclid_intros
  euclid_apply (sum_parallelograms_area a d c n h g AD CN AB DE)
  euclid_finish

end Elements.Book2
