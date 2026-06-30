import SystemE

namespace Elements.Book2

-- Package the rectangle BD's parallelogram structure once (atoms come straight from
-- proposition_42's conclusion). Reused by the area steps 1, 2, 3, 18 via the `have fp` in Main.
set_option systemE.solverTime 30 in
theorem helper_2_14_fp
    (e d b₀ c₀ : Point) (ED B₀C₀ BE DC : Line)
    (h_eED : e.onLine ED) (h_dED : d.onLine ED)
    (h_b0B0C0 : b₀.onLine B₀C₀) (h_c0B0C0 : c₀.onLine B₀C₀)
    (h_eBE : e.onLine BE) (h_b0BE : b₀.onLine BE)
    (h_dDC : d.onLine DC) (h_c0DC : c₀.onLine DC) (h_dc0 : d ≠ c₀)
    (h_ss : e.sameSide b₀ DC)
    (h_ni1 : ¬ED.intersectsLine B₀C₀) (h_ni2 : ¬BE.intersectsLine DC) :
    formParallelogram e d b₀ c₀ ED B₀C₀ BE DC := by
  exact ⟨h_eED, h_dED, h_b0B0C0, h_c0B0C0, h_eBE, h_b0BE, ⟨h_dDC, h_c0DC, h_dc0⟩, h_ss, h_ni1, h_ni2⟩

end Elements.Book2
