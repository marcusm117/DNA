import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.22 sub: HGFD is right-angled. The corner at d, ∠ f:d:h, equals the square's right angle
   ∠ a:d:e (ray d→f along DE = d→e, ray d→h along AD = d→a — step22_fdh). Then the parallelogram
   HGFD has ∠ h:d:f = ∠ h:g:f (proposition_34', opposite angles) and the co-interior pairs sum to
   two right angles, forcing all four angles right. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step22_ra (h g f d : Point) (HK DE AD CF : Line)
    (hpar : formParallelogram h g d f HK DE AD CF)
    (hfdh : ∠ f:d:h = ∟) :
    (∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟) := by
  euclid_intros
  euclid_apply (proposition_34' h g d f HK DE AD CF)
  euclid_finish

end Elements.Book2
