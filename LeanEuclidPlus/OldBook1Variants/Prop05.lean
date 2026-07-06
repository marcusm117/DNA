import SystemE
import OldBook1.Prop03
import OldBook1.Prop04
import OldBook1.Prop05

namespace Elements.Book1

theorem proposition_5' : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) →
  (∠ a:b:c = ∠ a:c:b) :=
by
  euclid_intros
  euclid_apply (extend_point AB a b) as d
  euclid_apply (extend_point AC a c) as e
  euclid_apply (proposition_5 a b c d e AB BC AC)
  euclid_finish

end Elements.Book1
