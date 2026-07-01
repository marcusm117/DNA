import SystemE

namespace Elements.Book2

-- step 3 (BE = ED case): the rectangle area equals |b₀─e|² (BD is a square on BE).
-- Same shape as step 2 (takes the standalone `step1` for the right angle); symmetry facts fed
-- explicitly so euclid_finish proves area = |b₀─e|² directly rather than wandering to △a:b:c.
set_option systemE.solverTime 30 in
theorem helper_2_14_step3
    (a b c q e d b₀ c₀ : Point) (ED B₀C₀ BE DC : Line)
    (fp : formParallelogram e d b₀ c₀ ED B₀C₀ BE DC)
    (step1 : Triangle.area △b₀:e:d + Triangle.area △b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟)
    (heq : |(b₀─e)| = |(e─d)|) :
    Triangle.area △b₀:e:d + Triangle.area △b₀:c₀:d = |(b₀─e)| * |(b₀─e)| := by
  have hra : (∠ e:b₀:c₀ : ℝ) = ∟ := by euclid_finish
  have hrect := rectangle_area e d b₀ c₀ ED B₀C₀ BE DC ⟨fp, hra⟩
  have hs1 : Triangle.area △ d:e:b₀ = Triangle.area △ b₀:e:d := by euclid_finish
  have hs2 : Triangle.area △ d:c₀:b₀ = Triangle.area △ b₀:c₀:d := by euclid_finish
  have heb0 : |(e─b₀)| = |(b₀─e)| := by euclid_finish
  euclid_finish

end Elements.Book2
