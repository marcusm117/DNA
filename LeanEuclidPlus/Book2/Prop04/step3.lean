import SystemE
import Book.Prop05

namespace Elements.Book2

open Elements.Book1

-- 2.4.3: in triangle ABD, BA = AD ⟹ base angles ∠ADB = ∠ABD  [Prop.~1.5] (pons asinorum).
set_option systemE.solverTime 30 in
theorem helper_2_step3 (a b d : Point) (AB BD AD : Line)
    (htri : formTriangle a b d AB BD AD) (hadab : |(a─d)| = |(a─b)|) :
    ∠ a:d:b = ∠ a:b:d := by
  euclid_intros
  euclid_apply (proposition_5' a b d AB BD AD)
  euclid_finish

end Elements.Book2
