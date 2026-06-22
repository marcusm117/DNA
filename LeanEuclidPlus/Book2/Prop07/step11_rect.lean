import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.11 sub: area(DG = DHGN) = |h─d| * |h─g|. rectangle_area on formParallelogram h g d n HF DE AD CN
   with the right angle ∠ h:d:n = ∟ (vertex d in the c-slot) gives △h:d:n + △h:g:n = |h─g|·|h─d|;
   by area symmetry this is the DG triangulation △d:h:g + △d:g:n. -/
theorem helper_2_7_step11_rect (h g d n : Point) (HF DE AD CN : Line)
    (hpar : formParallelogram h g d n HF DE AD CN)
    (hhdn : ∠ h:d:n = ∟) :
    Triangle.area △ d:h:g + Triangle.area △ d:g:n = |(h─d)| * |(h─g)| := by
  euclid_intros
  euclid_apply (rectangle_area h g d n HF DE AD CN)
  euclid_finish

end Elements.Book2
