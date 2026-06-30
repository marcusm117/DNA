import SystemE
import Helpers.OffLine
import Helpers.Parallel
import Mathlib.Tactic.Ring
import Book2.Prop11.step8_pyth
import Book2.Prop11.step8_bisect
import Book2.Prop11.step8_eb
import Book2.Prop11.step8_ahb_mag
import Book2.Prop11.between_ahb
import Book2.Prop11.step9_eaf
import Book2.Prop11.step16_ahab
import Book2.Prop11.step16_fnab
import Book2.Prop11.step21_par
import Book2.Prop11.step21_rangle
import Book2.Prop11.step21_dkbh
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step21
    (a b c d e f f0 g h x k : Point) (AB CD AC BD GH AH FG : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hkGH : k.onLine GH)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hkCD : k.onLine CD)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hdb : d ≠ b)
    (hac_ab : |(a─c)| = |(a─b)|) (hah_af : |(a─h)| = |(a─f)|) (hae_ec : |(a─e)| = |(e─c)|)
    (hang_acd : ∠ a:c:d = ∟) (hang_bac : ∠ b:a:c = ∟) (hang_fah : ∠ f:a:h = ∟) (hang_abd : ∠ a:b:d = ∟)
    (hbet_aec : between a e c) (hbet_caf0 : between c a f0) (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|)
    (hAHFG : ¬AH.intersectsLine FG)
    (hGHAC : ¬GH.intersectsLine AC)
    (hCDAB : ¬CD.intersectsLine AB)
    (hACBD : ¬AC.intersectsLine BD)
    (hboff : ¬b.onLine AC) (hhoff : ¬h.onLine AC)
    (hxoff : ¬x.onLine AC) (hhnsx : ¬h.sameSide x AC) (hxnsb : ¬x.sameSide b AC)
    -- @assumption: "$AB$ (is) equal to $BD$"
    (hbd_ab : |(b─d)| = |(a─b)|) :
    Triangle.area △ h:b:d + Triangle.area △ h:k:d = |(a─b)| * |(b─h)| := by
  -- magnitude tower ⟹ between a h b (needed for the right angle ∠d:b:h = ∠a:b:d).
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_apply (helper_2_11_step8_pyth a b c e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)))
  have step8_bisect : |(a─b)| = |(a─e)| + |(a─e)| := by euclid_apply (helper_2_11_step8_bisect a b c e (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)))
  have step8_eb : |(e─b)| = |(a─e)| + |(a─f)| := by euclid_apply (helper_2_11_step8_eb a b c e f f0 AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)))
  have step8_ahb_mag : |(a─f)| < |(a─b)| := by euclid_apply (helper_2_11_step8_ahb_mag a b e f (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a─e)| + |(a─e)|; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)) (by euclid_assumption "" (show |(e─b)| = |(a─e)| + |(a─f)|; assumption)))
  have between_ahb : between a h b := by euclid_apply (helper_2_11_between_ahb a b c e f f0 h g x AB AC AH GH CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show ¬ x.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show ¬ h.onLine AC; assumption)) (by euclid_assumption "" (show ¬ x.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬ h.sameSide x AC; assumption)))
  have step9_eaf : between e a f := by euclid_apply (helper_2_11_step9_eaf a b c e f f0 AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)))
  have hcaf : between c a f := by euclid_finish
  -- BD ∥ GH (re-derived: BD ∥ AC ∥ GH).
  have step16_ahab : AH = AB := by euclid_apply (helper_2_11_step16_ahab a b h f c x AH AB AC (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between c a f; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show ¬x.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.sameSide x AC; assumption)) (by euclid_assumption "" (show ¬x.sameSide b AC; assumption)))
  have step16_fnab : ¬f.onLine AB := by euclid_apply (helper_2_11_step16_fnab a b c f AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between c a f; assumption)))
  have hhAB : h.onLine AB := step16_ahab ▸ hhAH
  have hbh : b ≠ h := by euclid_finish
  have hABFG : ¬AB.intersectsLine FG := step16_ahab ▸ hAHFG
  have hFGAB : ¬FG.intersectsLine AB := fun hh => hABFG (intersection_symm FG AB hh)
  have hFGneAB : FG ≠ AB := line_ne_of_offLine f FG AB hfFG step16_fnab
  have hg_nAB : ¬g.onLine AB := offLine_of_parallel_simple g FG AB hgFG hFGneAB hFGAB
  have hb_nGH : ¬b.onLine GH := offLine_of_two_points b h g AB GH hbAB hhAB hbh hhGH hgGH hg_nAB
  have hBDneGH : BD ≠ GH := line_ne_of_offLine b BD GH hbBD hb_nGH
  have hACGH : ¬AC.intersectsLine GH := fun hh => hGHAC (intersection_symm AC GH hh)
  have hACneGH : AC ≠ GH := (line_ne_of_offLine h GH AC hhGH hhoff).symm
  have hBDneAC : BD ≠ AC := line_ne_of_offLine b BD AC hbBD hboff
  have hBDAC : ¬BD.intersectsLine AC := fun hh => hACBD (intersection_symm BD AC hh)
  have hBDGH : ¬BD.intersectsLine GH := not_intersects_trans BD AC GH hBDAC hACGH hBDneAC hACneGH hBDneGH
  -- k ≠ h on GH, and k ≠ b (b is off GH).
  have hkh : k ≠ h := by euclid_finish
  have hkb : k ≠ b := fun heq => hb_nGH (heq ▸ hkGH)
  -- assemble HBDK as formParallelogram d k b h, the right angle, and |dk| = |bh|.
  have step21_par : formParallelogram d k b h CD AB BD GH := by euclid_apply (helper_2_11_step21_par d k b h CD AB BD GH (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine GH; assumption)) (by euclid_assumption "" (show BD ≠ GH; assumption)) (by euclid_assumption "" (show k ≠ h; assumption)))
  have step21_rangle : ∠ d:b:h = ∟ := by euclid_apply (helper_2_11_step21_rangle a b d h AB BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show between a h b; assumption)) (by euclid_assumption "" (show ∠ a:b:d = ∟; assumption)))
  have step21_dkbh : |(d─k)| = |(b─h)| := by euclid_apply (helper_2_11_step21_dkbh d k b h CD AB BD GH (by euclid_assumption "" (show formParallelogram d k b h CD AB BD GH; assumption)) (by euclid_assumption "" (show k ≠ b; assumption)))
  -- rectangle_area on HBDK + length recast.
  obtain ⟨h1, _⟩ := rectangle_area d k b h CD AB BD GH ⟨step21_par, step21_rangle⟩
  have p1 : Triangle.area △ d:b:h = Triangle.area △ h:b:d := (area_symm_1 d b h).trans (area_symm_2 h d b)
  have p2 : Triangle.area △ d:k:h = Triangle.area △ h:k:d := (area_symm_1 d k h).trans (area_symm_2 h d k)
  have hdb : |(d─b)| = |(a─b)| := by rw [segment_symmetric d b]; exact hbd_ab
  rw [step21_dkbh, hdb, p1, p2] at h1
  rw [h1]; ring

end Elements.Book2
