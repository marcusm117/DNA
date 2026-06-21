import SystemE

namespace Elements.Book2

theorem proposition_12 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ (∠ b:a:c : ℝ) > ∟ ∧
  d.onLine CA ∧ between d a c ∧ (∠ b:d:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| =
    |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) := by
  sorry

end Elements.Book2
