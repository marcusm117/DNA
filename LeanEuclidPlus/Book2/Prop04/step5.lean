import SystemE
import Book.Prop06

namespace Elements.Book2

open Elements.Book1

-- 2.4.5: in triangle CGB, base angles ∠CGB = ∠GBC equal ⟹ sides BC = CG  [Prop.~1.6].
-- proposition_6 with apex c, base vertices g,b: ∠CGB = ∠CBG ⟹ |CG| = |CB|.
set_option systemE.solverTime 30 in
theorem helper_2_step5 (b c g : Point) (CG GB CB : Line)
    (htri : formTriangle c g b CG GB CB) (hang : ∠ c:g:b = ∠ g:b:c) :
    |(b─c)| = |(c─g)| := by
  euclid_intros
  euclid_apply (proposition_6 c g b CG GB CB)
  euclid_finish

end Elements.Book2
