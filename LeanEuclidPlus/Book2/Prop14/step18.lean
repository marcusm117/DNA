import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 18: BD is the rectangle contained by BE and EF. By rectangle_area the parallelogram's area
-- (the two triangles) equals |e─d|·|e─b₀|; and EF = ED (step6), so it equals |b₀─e|·|e─f|.
-- (formParallelogram e d b₀ c₀ ED B₀C₀ BE DC supplied via its atoms.)
theorem helper_2_14_step18 (e d b₀ c₀ f : Point) (ED B₀C₀ BE DC : Line)
    (h_eED : e.onLine ED) (h_dED : d.onLine ED)
    (h_b0BC : b₀.onLine B₀C₀) (h_c0BC : c₀.onLine B₀C₀)
    (h_eBE : e.onLine BE) (h_b0BE : b₀.onLine BE)
    (h_dDC : d.onLine DC) (h_c0DC : c₀.onLine DC) (h_dc0 : d ≠ c₀)
    (h_esb0 : e.sameSide b₀ DC)
    (h_par1 : ¬ED.intersectsLine B₀C₀) (h_par2 : ¬BE.intersectsLine DC)
    (h_rang : ∠ c₀:b₀:e = ∟)
    (h_ef : |(e─f)| = |(e─d)|) :
    (△ b₀:e:d).area + (△ b₀:c₀:d).area = |(b₀─e)| * |(e─f)| := by
  have hfp : formParallelogram e d b₀ c₀ ED B₀C₀ BE DC := by
    unfold formParallelogram distinctPointsOnLine
    euclid_finish
  have hr2 : (∠ e:b₀:c₀ : ℝ) = ∟ := by euclid_finish
  have hrect := rectangle_area e d b₀ c₀ ED B₀C₀ BE DC ⟨hfp, hr2⟩
  -- hrect.2 : △d:e:b₀ + △d:c₀:b₀ = |e─d|·|e─b₀|  (rectangle area, e‑side product)
  have hs1 : Triangle.area △ d:e:b₀ = Triangle.area △ b₀:e:d := by euclid_finish
  have hs2 : Triangle.area △ d:c₀:b₀ = Triangle.area △ b₀:c₀:d := by euclid_finish
  have heb0 : |(e─b₀)| = |(b₀─e)| := by euclid_finish
  euclid_finish

end Elements.Book2
