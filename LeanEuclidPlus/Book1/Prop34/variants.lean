import SystemE
import Book1.Prop26.Main
import Book1.Prop29.variants
import Book1.Prop34.Main

namespace Elements.Book1

theorem proposition_34' : ∀ (a b c d : Point) (AB CD AC BD : Line),
  formParallelogram a b c d AB CD AC BD →
  |(a─b)| = |(c─d)| ∧ |(a─c)| = |(b─d)| ∧
  ∠ a:b:d = ∠ a:c:d ∧ ∠ b:a:c = ∠ c:d:b :=
by
  euclid_intros
  euclid_apply (line_from_points b c) as BC
  euclid_apply (proposition_34 a b c d AB CD AC BD BC)
  euclid_finish

end Elements.Book1
