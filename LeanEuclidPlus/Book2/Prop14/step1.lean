import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 1: the right-angled parallelogram BD (corners b₀=B, e=E, d=D, c₀=C) has area equal to
-- the rectilinear figure A (the quadrilateral a:b:c:q, area △a:b:q + △q:b:c) and a right angle at b₀.
-- prop45 gives the area via the e‑c₀ diagonal (△e:b₀:c₀ + △e:d:c₀); `parallelogram_area` re-expresses
-- it via the b₀‑d diagonal that the claim uses; the right angle is ∠c₀:b₀:e = ∠e:b₀:c₀ = ∠p:a:b = ∟.
theorem helper_2_14_step1
    (a b c q e d b₀ c₀ p : Point) (ED B₀C₀ BE DC : Line)
    (h_eED : e.onLine ED) (h_dED : d.onLine ED)
    (h_b0B0C0 : b₀.onLine B₀C₀) (h_c0B0C0 : c₀.onLine B₀C₀)
    (h_eBE : e.onLine BE) (h_b0BE : b₀.onLine BE)
    (h_dDC : d.onLine DC) (h_c0DC : c₀.onLine DC) (h_dc0 : d ≠ c₀)
    (h_ss : e.sameSide b₀ DC)
    (h_ni1 : ¬ED.intersectsLine B₀C₀) (h_ni2 : ¬BE.intersectsLine DC)
    (hang : ∠ e:b₀:c₀ = ∠ p:a:b) (hr : ∠ p:a:b = ∟)
    (harea : Triangle.area △e:b₀:c₀ + Triangle.area △e:d:c₀ = Triangle.area △ a:b:q + Triangle.area △ q:b:c) :
    Triangle.area △b₀:e:d + Triangle.area △b₀:c₀:d = Triangle.area △ a:b:q + Triangle.area △ q:b:c ∧ ∠ c₀:b₀:e = ∟ := by
  refine ⟨?_, ?_⟩
  · -- area: re-express the e‑c₀ diagonal area (prop45) via the b₀‑d diagonal (parallelogram_area)
    euclid_apply (parallelogram_area e d b₀ c₀ ED B₀C₀ BE DC)
    euclid_finish
  · -- right angle: ∠c₀:b₀:e = ∠e:b₀:c₀ = ∠p:a:b = ∟
    euclid_finish

end Elements.Book2
