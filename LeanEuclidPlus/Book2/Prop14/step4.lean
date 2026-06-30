import SystemE

namespace Elements.Book2

-- step 4 (BE ≠ ED case): one of BE, ED is greater than the other (trichotomy).
set_option systemE.solverTime 30 in
theorem helper_2_14_step4 (b₀ e d : Point) (hne : |(b₀─e)| ≠ |(e─d)|) :
    |(b₀─e)| > |(e─d)| ∨ |(e─d)| > |(b₀─e)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · -- |b₀─e| < |e─d|  ⟹  (by `>` defeq)  |e─d| > |b₀─e|
    right; exact h
  · -- |b₀─e| > |e─d|
    left; exact h

end Elements.Book2
