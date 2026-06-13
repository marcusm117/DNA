import SystemE
import Book.Prop31
import Book.Prop46

namespace Elements.Book2

open Elements.Book1


set_option systemE.solverTime 30 in
theorem proposition_2 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  |(a─b)| * |(b─c)| + |(b─a)| * |(a─c)| = |(a─b)| * |(a─b)| :=
by
  sorry
end Elements.Book2
