import SystemE
import Helpers.OffLine
import Helpers.Parallel
import Mathlib.Tactic.Linarith
import Book2.Prop11.step8_pyth
import Book2.Prop11.step9_eaf
import Book2.Prop11.step16_ahab
import Book2.Prop11.step16_ancd
import Book2.Prop11.step16_fncd
import Book2.Prop11.step16_fnab
import Book2.Prop11.step16_fgcd
import Book2.Prop11.step19_ghk
import Book2.Prop11.step8_bisect
import Book2.Prop11.step8_eb
import Book2.Prop11.step8_ahb_mag
import Book2.Prop11.between_ahb
import Book2.Prop11.step19_ckd
import Book2.Prop11.step16_par
import Book2.Prop11.step17_par
import Book2.Prop11.step19_fk
import Book2.Prop11.step19_ad
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step19
    (a b c d e f f0 g h x k : Point) (AB CD AC BD GH AH FG : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hkGH : k.onLine GH)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hkCD : k.onLine CD)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hdb : d ≠ b)
    (hca_ss : c.sameSide a BD)
    (hcd_ab : |(c─d)| = |(a─b)|) (hac_ab : |(a─c)| = |(a─b)|)
    (hah_af : |(a─h)| = |(a─f)|) (hae_ec : |(a─e)| = |(e─c)|)
    (hang_acd : ∠ a:c:d = ∟) (hang_bac : ∠ b:a:c = ∟) (hang_fah : ∠ f:a:h = ∟)
    (hbet_aec : between a e c) (hbet_caf0 : between c a f0) (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|)
    (hAHFG : ¬AH.intersectsLine FG)
    (hCDAB : ¬CD.intersectsLine AB)
    (hGHAC : ¬GH.intersectsLine AC)
    (hACBD : ¬AC.intersectsLine BD)
    (hxoff : ¬x.onLine AC) (hboff : ¬b.onLine AC) (hhoff : ¬h.onLine AC)
    (hhnsx : ¬h.sameSide x AC) (hxnsb : ¬x.sameSide b AC)
    (hstep18 : Triangle.area △ f:g:k + Triangle.area △ f:c:k = Triangle.area △ a:b:d + Triangle.area △ a:c:d) :
    Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d := by
  -- order facts on the left line.
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_apply (helper_2_11_step8_pyth a b c e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)))
  have step9_eaf : between e a f := by euclid_apply (helper_2_11_step9_eaf a b c e f f0 AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)))
  have hcaf : between c a f := by euclid_finish
  have hfac : between f a c := by euclid_finish
  -- AH = AB and the FG ∥ AB ∥ CD chain (re-derived as in step16).
  have step16_ahab : AH = AB := by euclid_apply (helper_2_11_step16_ahab a b h f c x AH AB AC (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between c a f; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show ¬x.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.sameSide x AC; assumption)) (by euclid_assumption "" (show ¬x.sameSide b AC; assumption)))
  have step16_ancd : ¬a.onLine CD := by euclid_apply (helper_2_11_step16_ancd a b c d e AC CD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─b)|; assumption)))
  have step16_fncd : ¬f.onLine CD := by euclid_apply (helper_2_11_step16_fncd a b c d f AC CD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show between c a f; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─b)|; assumption)))
  have step16_fnab : ¬f.onLine AB := by euclid_apply (helper_2_11_step16_fnab a b c f AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between c a f; assumption)))
  have hhAB : h.onLine AB := step16_ahab ▸ hhAH
  have hABFG : ¬AB.intersectsLine FG := step16_ahab ▸ hAHFG
  have hFGAB : ¬FG.intersectsLine AB := fun hh => hABFG (intersection_symm FG AB hh)
  have hABCD : ¬AB.intersectsLine CD := fun hh => hCDAB (intersection_symm AB CD hh)
  have hFGneAB : FG ≠ AB := line_ne_of_offLine f FG AB hfFG step16_fnab
  have hABneCD : AB ≠ CD := line_ne_of_offLine a AB CD haAB step16_ancd
  have hCDneAB : CD ≠ AB := hABneCD.symm
  have hFGneCD : FG ≠ CD := line_ne_of_offLine f FG CD hfFG step16_fncd
  have step16_fgcd : ¬FG.intersectsLine CD := by euclid_apply (helper_2_11_step16_fgcd FG AB CD (by euclid_assumption "" (show ¬FG.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show FG ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ CD; assumption)) (by euclid_assumption "" (show FG ≠ CD; assumption)))
  -- AC ∥ GH facts.
  have hACGH : ¬AC.intersectsLine GH := fun hh => hGHAC (intersection_symm AC GH hh)
  have hACneGH : AC ≠ GH := (line_ne_of_offLine h GH AC hhGH hhoff).symm
  have ha_nGH : ¬a.onLine GH := offLine_of_parallel a h AC GH haAC hhGH hhoff hGHAC
  have hABneGH : AB ≠ GH := line_ne_of_offLine a AB GH haAB ha_nGH
  -- foot h between g and k on GH.
  have step19_ghk : between g h k := by euclid_apply (helper_2_11_step19_ghk a b c f g h k AB AC FG CD GH (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show between f a c; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show FG ≠ AB; assumption)) (by euclid_assumption "" (show CD ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ GH; assumption)))
  -- magnitude tower ⟹ between a h b.
  have step8_bisect : |(a─b)| = |(a─e)| + |(a─e)| := by euclid_apply (helper_2_11_step8_bisect a b c e (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)))
  have step8_eb : |(e─b)| = |(a─e)| + |(a─f)| := by euclid_apply (helper_2_11_step8_eb a b c e f f0 AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)))
  have step8_ahb_mag : |(a─f)| < |(a─b)| := by euclid_apply (helper_2_11_step8_ahb_mag a b e f (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a─e)| + |(a─e)|; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)) (by euclid_assumption "" (show |(e─b)| = |(a─e)| + |(a─f)|; assumption)))
  have between_ahb : between a h b := by euclid_apply (helper_2_11_between_ahb a b c e f f0 h g x AB AC AH GH CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show ¬ x.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show ¬ h.onLine AC; assumption)) (by euclid_assumption "" (show ¬ x.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬ h.sameSide x AC; assumption)))
  -- BD ∥ GH and GH ≠ CD, then foot k between c and d on CD.
  have hbh : b ≠ h := by euclid_finish
  have hh_nCD : ¬h.onLine CD := offLine_of_parallel_simple h AB CD hhAB hABneCD hABCD
  have hGHneCD : GH ≠ CD := line_ne_of_offLine h GH CD hhGH hh_nCD
  have hg_nAB : ¬g.onLine AB := offLine_of_parallel_simple g FG AB hgFG hFGneAB hFGAB
  have hb_nGH : ¬b.onLine GH := offLine_of_two_points b h g AB GH hbAB hhAB hbh hhGH hgGH hg_nAB
  have hBDneGH : BD ≠ GH := line_ne_of_offLine b BD GH hbBD hb_nGH
  have hBDneAC : BD ≠ AC := line_ne_of_offLine b BD AC hbBD hboff
  have hBDAC : ¬BD.intersectsLine AC := fun hh => hACBD (intersection_symm BD AC hh)
  have hBDGH : ¬BD.intersectsLine GH := not_intersects_trans BD AC GH hBDAC hACGH hBDneAC hACneGH hBDneGH
  have step19_ckd : between c k d := by euclid_apply (helper_2_11_step19_ckd a b c d h k AC BD GH CD (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show between a h b; assumption)) (by euclid_assumption "" (show ¬AC.intersectsLine GH; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine GH; assumption)) (by euclid_assumption "" (show AC ≠ GH; assumption)) (by euclid_assumption "" (show BD ≠ GH; assumption)) (by euclid_assumption "" (show GH ≠ CD; assumption)))
  -- the two parallelograms.
  have step16_par : formParallelogram f c g k AC GH FG CD := by euclid_apply (helper_2_11_step16_par f c g k h AC GH FG CD (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine CD; assumption)) (by euclid_assumption "" (show FG ≠ CD; assumption)))
  have step17_par : formParallelogram a b c d AB CD AC BD := by euclid_apply (helper_2_11_step17_par a b c d AB CD AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide a BD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AC.intersectsLine BD; assumption)))
  -- the two rectangle splits (FK = FH + AK ; AD = AK + HD).
  have step19_fk : Triangle.area △ f:g:h + Triangle.area △ f:a:h + Triangle.area △ a:h:k + Triangle.area △ a:k:c
      = Triangle.area △ f:g:k + Triangle.area △ f:c:k := by euclid_apply (helper_2_11_step19_fk a c f g h k AC GH FG CD (by euclid_assumption "" (show formParallelogram f c g k AC GH FG CD; assumption)) (by euclid_assumption "" (show between f a c; assumption)) (by euclid_assumption "" (show between g h k; assumption)))
  have step19_ad : Triangle.area △ a:h:k + Triangle.area △ a:k:c + Triangle.area △ h:k:d + Triangle.area △ h:b:d
      = Triangle.area △ a:c:d + Triangle.area △ a:b:d := by euclid_apply (helper_2_11_step19_ad a b c d h k AB CD AC BD (by euclid_assumption "" (show formParallelogram a b c d AB CD AC BD; assumption)) (by euclid_assumption "" (show between a h b; assumption)) (by euclid_assumption "" (show between c k d; assumption)))
  linarith [hstep18, step19_fk, step19_ad]

end Elements.Book2
