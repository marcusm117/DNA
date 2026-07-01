import SystemE

namespace Elements.Book2

-- step 8: the semicircle BHF is centred at G and passes through B and F (from circle_from_points g b₀
-- and point_on_circle_if g b₀ f BHF, both established in Main before this sentence).
set_option systemE.solverTime 30 in
theorem helper_2_14_step8 (g b₀ f : Point) (BHF : Circle)
    (h_ctr : g.isCentre BHF) (h_b0 : b₀.onCircle BHF) (h_f : f.onCircle BHF) :
    g.isCentre BHF ∧ b₀.onCircle BHF ∧ f.onCircle BHF := ⟨h_ctr, h_b0, h_f⟩

end Elements.Book2
