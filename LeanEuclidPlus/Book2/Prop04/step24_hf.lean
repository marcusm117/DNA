import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.24 sub: area(HGFD) = |a─c|². HGFD is a parallelogram (hpar) with the right angle at d,
   ∠ h:d:f = ∟, so by rectangle_area its area (△h:d:f + △h:g:f) = |h─g|·|h─d|; with |h─d| = |h─g|
   (HGFD equilateral) and |h─g| = |a─c| (step23), this is |a─c|·|a─c|. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step24_hf (a c h g f d : Point) (HK DE AD CF : Line)
    (hpar : formParallelogram h g d f HK DE AD CF)
    (hfdh : ∠ f:d:h = ∟) (hdf : d ≠ f) (hdh : d ≠ h)
    (heq1 : |(g─f)| = |(f─d)|) (heq2 : |(f─d)| = |(d─h)|) (heq3 : |(h─g)| = |(g─f)|)
    (hhgac : |(h─g)| = |(a─c)|) :
    Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)| := by
  euclid_intros
  have hhdf : (∠ h:d:f : ℝ) = ∟ := by rw [angle_symm h d f ⟨hdh.symm, hdf⟩]; exact hfdh
  have hrect : Triangle.area △ h:d:f + Triangle.area △ h:g:f = |(h─g)| * |(h─d)| := by
    euclid_apply (rectangle_area h g d f HK DE AD CF)
    euclid_finish
  euclid_finish

end Elements.Book2
