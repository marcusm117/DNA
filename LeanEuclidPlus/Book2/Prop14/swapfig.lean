import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- WLOG reduction support: the rectangle BEDC relabelled B↔D (so the greater side ED plays the role of
-- "BE"). Every conjunct is a fact of the SAME rectangle, so it follows from the original figure's atoms:
-- the right angle moves to D (parallel-angle chain), the parallelogram is the same corners reordered,
-- areas are permutations, and the length facts are `segment_symmetric` images of heq/step4/hgt. Proven in
-- isolation (small context) so the right-angle derivation that drowned in Main's full context is cheap.
set_option systemE.solverTime 30 in
theorem helper_2_14_swapfig
    (a b c q p e d b₀ c₀ : Point) (ED B₀C₀ BE DC : Line)
    (h_pab : ∠ p:a:b = ∟)
    (h_ebc : ∠ e:b₀:c₀ = ∠ p:a:b)
    (h_area : Triangle.area △ e:b₀:c₀ + Triangle.area △ e:d:c₀ = Triangle.area △ a:b:q + Triangle.area △ q:b:c)
    (h_eED : e.onLine ED) (h_dED : d.onLine ED)
    (h_b0B0C0 : b₀.onLine B₀C₀) (h_c0B0C0 : c₀.onLine B₀C₀)
    (h_eBE : e.onLine BE) (h_b0BE : b₀.onLine BE)
    (h_dDC : d.onLine DC) (h_c0DC : c₀.onLine DC)
    (h_ss : e.sameSide b₀ DC) (h_dc0 : d ≠ c₀)
    (h_ni1 : ¬ED.intersectsLine B₀C₀) (h_ni2 : ¬BE.intersectsLine DC)
    (hfp : formParallelogram e d b₀ c₀ ED B₀C₀ BE DC)
    (hstep1 : Triangle.area △ b₀:e:d + Triangle.area △ b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟)
    (heq : ¬ |(b₀─e)| = |(e─d)|)
    (hstep4 : |(b₀─e)| > |(e─d)| ∨ |(e─d)| > |(b₀─e)|)
    (hgt : ¬ |(b₀─e)| > |(e─d)|) :
    ∠ e:d:c₀ = ∠ p:a:b
    ∧ b₀ ≠ c₀
    ∧ e.sameSide d B₀C₀
    ∧ formParallelogram e b₀ d c₀ BE DC ED B₀C₀
    ∧ (Triangle.area △ d:e:b₀ + Triangle.area △ d:c₀:b₀ = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:d:e = ∟)
    ∧ (Triangle.area △ e:d:c₀ + Triangle.area △ e:b₀:c₀ = Triangle.area △ a:b:q + Triangle.area △ q:b:c)
    ∧ (¬ |(d─e)| = |(e─b₀)|)
    ∧ (|(d─e)| > |(e─b₀)| ∨ |(e─b₀)| > |(d─e)|)
    ∧ |(d─e)| > |(e─b₀)| := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book2
