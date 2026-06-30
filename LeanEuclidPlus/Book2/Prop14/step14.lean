import SystemE

namespace Elements.Book2

open Elements

-- step 14 [Prop. 1.47]: Pythagoras on the right triangle G:E:H, right angle ∠G:E:H at e
-- (ED ⟂ BE at the rectangle corner — see step14_perp). H on ED beyond e, G on BE.
-- The construction is unconditional, so E may coincide with G (BE = ED degenerate case) — then
-- there is no triangle and the identity is trivial.
set_option systemE.solverTime 30 in
theorem helper_2_14_step14 (e d b₀ c₀ g h f : Point) (ED B₀C₀ BE DC GH : Line)
    (h_eED : e.onLine ED) (h_dED : d.onLine ED) (h_hED : h.onLine ED)
    (h_b0BC : b₀.onLine B₀C₀) (h_c0BC : c₀.onLine B₀C₀)
    (h_b0BE : b₀.onLine BE) (h_eBE : e.onLine BE) (h_fBE : f.onLine BE)
    (h_dDC : d.onLine DC) (h_c0DC : c₀.onLine DC)
    (h_rang : ∠ c₀:b₀:e = ∟)
    (h_par1 : ¬ED.intersectsLine B₀C₀) (h_par2 : ¬BE.intersectsLine DC)
    (h_esb0 : e.sameSide b₀ DC)
    (h_bet_hed : between h e d) (h_bef : between b₀ e f)
    (h_gGH : g.onLine GH) (h_hGH : h.onLine GH)
    (h_bgf : between b₀ g f) :
    |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)| := by
  euclid_intros
  have step14_ss : d.sameSide c₀ BE := by sorry
  have step14_rt0 : ∠ b₀:e:h = ∟ := by sorry
  have step14_hoff : ¬ h.onLine BE := by sorry
  have step14_pyth : |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)| := by sorry
  exact step14_pyth

end Elements.Book2
