import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.8 sub: area(AF = ABFH) = |h─f| * |h─a|. rectangle_area on formParallelogram h f a b HF AB AD BE
   with the right angle ∠ h:a:b = ∟ (vertex a in the c-slot) gives △h:a:b + △h:f:b = |h─f|·|h─a|;
   by area symmetry this is the AF triangulation △a:b:f + △a:f:h. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step8_rectAF (h f a b : Point) (HF AB AD BE : Line)
    (hpar : formParallelogram h f a b HF AB AD BE)
    (hhab : ∠ h:a:b = ∟) :
    Triangle.area △ a:b:f + Triangle.area △ a:f:h = |(h─f)| * |(h─a)| := by
  euclid_intros
  euclid_apply (rectangle_area h f a b HF AB AD BE)
  euclid_finish

end Elements.Book2
