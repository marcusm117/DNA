import SystemE

namespace Elements.Book2

theorem proposition_10 : ∀ (a b c d : Point) (AD : Line),
  distinctPointsOnLine a d AD ∧ c.onLine AD ∧ b.onLine AD ∧
  between a c b ∧ between a b d ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
    2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  sorry

end Elements.Book2
