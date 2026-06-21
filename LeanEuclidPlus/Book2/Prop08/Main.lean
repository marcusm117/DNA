import SystemE

namespace Elements.Book2

theorem proposition_8 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  4 * (|(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| =
    (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|) := by
  sorry

end Elements.Book2
