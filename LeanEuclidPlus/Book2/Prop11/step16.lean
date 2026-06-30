import SystemE
import Helpers.OffLine
import Helpers.Parallel
import Book2.Prop11.step8_pyth
import Book2.Prop11.step9_eaf
import Book2.Prop11.step16_ahab
import Book2.Prop11.step16_ancd
import Book2.Prop11.step16_fncd
import Book2.Prop11.step16_fnab
import Book2.Prop11.step16_fgcd
import Book2.Prop11.step16_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step16
    (a b c d e f f0 g h x k : Point) (AB CD AC BD GH AH FG : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hkGH : k.onLine GH)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hkCD : k.onLine CD)
    (hcd_ab : |(c─d)| = |(a─b)|)
    (hang_acd : ∠ a:c:d = ∟)
    (hbet_aec : between a e c)
    (hbet_caf0 : between c a f0)
    (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|)
    (hang_bac : ∠ b:a:c = ∟) (hang_fah : ∠ f:a:h = ∟) (hang_fgh : ∠ f:g:h = ∟)
    (hAHFG : ¬AH.intersectsLine FG)
    (hCDAB : ¬CD.intersectsLine AB)
    (hGHAC : ¬GH.intersectsLine AC)
    (hxoff : ¬x.onLine AC) (hboff : ¬b.onLine AC) (hhoff : ¬h.onLine AC)
    (hhnsx : ¬h.sameSide x AC) (hxnsb : ¬x.sameSide b AC)
    -- @assumption: "$AF$ (is) equal to $FG$"
    (haf_fg : |(f─g)| = |(a─f)|) :
    Triangle.area △ f:g:k + Triangle.area △ f:c:k = |(c─f)| * |(f─a)| := by
  -- f lies beyond a, so a is between c and f (magnitude argument, reuses step9 cone).
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_apply (helper_2_11_step8_pyth a b c e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)))
  have step9_eaf : between e a f := by euclid_apply (helper_2_11_step9_eaf a b c e f f0 AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)))
  have hcaf : between c a f := by euclid_finish
  -- AH ⊥ AC and AB ⊥ AC at A, with h, b same side of AC ⟹ AH = AB.
  have step16_ahab : AH = AB := by euclid_apply (helper_2_11_step16_ahab a b h f c x AH AB AC (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between c a f; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show ¬x.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.sameSide x AC; assumption)) (by euclid_assumption "" (show ¬x.sameSide b AC; assumption)))
  -- off-line facts (slim leaves) feeding the line-≠ terms.
  have step16_ancd : ¬a.onLine CD := by euclid_apply (helper_2_11_step16_ancd a b c d e AC CD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─b)|; assumption)))
  have step16_fncd : ¬f.onLine CD := by euclid_apply (helper_2_11_step16_fncd a b c d f AC CD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show between c a f; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─b)|; assumption)))
  have step16_fnab : ¬f.onLine AB := by euclid_apply (helper_2_11_step16_fnab a b c f AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between c a f; assumption)))
  -- parallel transitivity FG ∥ AB ∥ CD ⟹ FG ∥ CD (zero-SMT terms + one slim leaf).
  have hABFG : ¬AB.intersectsLine FG := step16_ahab ▸ hAHFG
  have hFGAB : ¬FG.intersectsLine AB := fun hh => hABFG (intersection_symm FG AB hh)
  have hABCD : ¬AB.intersectsLine CD := fun hh => hCDAB (intersection_symm AB CD hh)
  have hFGneAB : FG ≠ AB := line_ne_of_offLine f FG AB hfFG step16_fnab
  have hABneCD : AB ≠ CD := line_ne_of_offLine a AB CD haAB step16_ancd
  have hFGneCD : FG ≠ CD := line_ne_of_offLine f FG CD hfFG step16_fncd
  have step16_fgcd : ¬FG.intersectsLine CD := by euclid_apply (helper_2_11_step16_fgcd FG AB CD (by euclid_assumption "" (show ¬FG.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show FG ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ CD; assumption)) (by euclid_assumption "" (show FG ≠ CD; assumption)))
  -- the rectangle FGKC is a parallelogram with a right angle at G.
  have step16_par : formParallelogram f c g k AC GH FG CD := by euclid_apply (helper_2_11_step16_par f c g k h AC GH FG CD (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine CD; assumption)) (by euclid_assumption "" (show FG ≠ CD; assumption)))
  have hrangle : ∠ f:g:k = ∟ := by euclid_finish
  -- rectangle_area: area△fgk + area△fck = |f-c|*|f-g|; recast to |c-f|*|f-a| by symmetry + AF=FG.
  have hfc : |(c─f)| = |(f─c)| := segment_symmetric c f
  have hfa : |(f─a)| = |(f─g)| := by rw [segment_symmetric f a]; exact haf_fg.symm
  rw [hfc, hfa]
  obtain ⟨h1, _⟩ := rectangle_area f c g k AC GH FG CD ⟨step16_par, hrangle⟩
  exact h1

end Elements.Book2
