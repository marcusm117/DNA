import SystemE
import Book2.Prop14.step14_ss
import Book2.Prop14.step14_rt0
import Book2.Prop14.step14_hoff
import Book2.Prop14.step14_pyth
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step 14 [Prop. 1.47]: Pythagoras on the right triangle G:E:H, right angle ∠G:E:H at e
-- (ED ⟂ BE at the rectangle corner — see step14_perp). H on ED beyond e, G on BE.
-- The construction is unconditional, so E may coincide with G (BE = ED degenerate case) — then
-- there is no triangle and the identity is trivial.
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
  have step14_ss : d.sameSide c₀ BE := by euclid_apply (helper_2_14_step14_ss d c₀ e b₀ DC BE (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c₀.onLine DC; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show e.sameSide b₀ DC; assumption)) (by euclid_assumption "" (show ¬BE.intersectsLine DC; assumption)))
  have step14_rt0 : ∠ b₀:e:h = ∟ := by euclid_apply (helper_2_14_step14_rt0 e d b₀ c₀ h f ED B₀C₀ BE (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show b₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show c₀.onLine B₀C₀; assumption)) (by euclid_assumption "" (show b₀.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ∠ c₀:b₀:e = ∟; assumption)) (by euclid_assumption "" (show ¬ED.intersectsLine B₀C₀; assumption)) (by euclid_assumption "" (show d.sameSide c₀ BE; assumption)) (by euclid_assumption "" (show between h e d; assumption)) (by euclid_assumption "" (show between b₀ e f; assumption)))
  have step14_hoff : ¬ h.onLine BE := by euclid_apply (helper_2_14_step14_hoff e b₀ h d f BE (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b₀.onLine BE; assumption)) (by euclid_assumption "" (show ∠ b₀:e:h = ∟; assumption)) (by euclid_assumption "" (show between b₀ e f; assumption)) (by euclid_assumption "" (show between h e d; assumption)))
  have step14_pyth : |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)| := by euclid_apply (helper_2_14_step14_pyth e b₀ g h f BE GH ED (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b₀.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine BE; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show h.onLine ED; assumption)) (by euclid_assumption "" (show between b₀ e f; assumption)) (by euclid_assumption "" (show between b₀ g f; assumption)) (by euclid_assumption "" (show ∠ b₀:e:h = ∟; assumption)) (by euclid_assumption "" (show ¬ h.onLine BE; assumption)))
  exact step14_pyth

end Elements.Book2
