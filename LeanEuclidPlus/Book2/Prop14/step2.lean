import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 2 (BE = ED case): BD is a square on BE, so |b₀─e|² = area A (= △a:b:q + △q:b:c).
-- rectangle_area gives area = |e─d|·|e─b₀|; with BE = ED (heq) and |e─b₀| = |b₀─e| this is |b₀─e|²,
-- and step 1 ties the rectangle area to A. (Symmetry facts fed explicitly so the chain closes.)
theorem helper_2_14_step2
    (a b c q e d b₀ c₀ : Point) (ED B₀C₀ BE DC : Line)
    (fp : formParallelogram e d b₀ c₀ ED B₀C₀ BE DC)
    (step1 : Triangle.area △b₀:e:d + Triangle.area △b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟)
    (heq : |(b₀─e)| = |(e─d)|)
    (h_bda : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c) :
    |(b₀─e)| * |(b₀─e)| = Triangle.area △ a:b:q + Triangle.area △ q:b:c := by
  have hra : (∠ e:b₀:c₀ : ℝ) = ∟ := by euclid_finish
  have hrect := rectangle_area e d b₀ c₀ ED B₀C₀ BE DC ⟨fp, hra⟩
  -- hrect.2 : △d:e:b₀ + △d:c₀:b₀ = |e─d|·|e─b₀|  (rectangle area, e‑side product)
  have hs1 : Triangle.area △ d:e:b₀ = Triangle.area △ b₀:e:d := by euclid_finish
  have hs2 : Triangle.area △ d:c₀:b₀ = Triangle.area △ b₀:c₀:d := by euclid_finish
  have heb0 : |(e─b₀)| = |(b₀─e)| := by euclid_finish
  euclid_finish

end Elements.Book2
