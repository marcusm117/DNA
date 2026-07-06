import SystemE
import Book1.Prop03.Main
import Book1.Prop04.Main
import Book1.Prop05.Main

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
