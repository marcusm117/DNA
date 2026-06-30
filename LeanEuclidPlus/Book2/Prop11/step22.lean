import SystemE
import Helpers.OffLine
import Book2.Prop11.step8_pyth
import Book2.Prop11.step9_eaf
import Book2.Prop11.step22_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_11_step22
    (a b c e f f0 g h : Point) (AB AC GH FG AH : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (hab : a ≠ b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbet_aec : between a e c) (hbet_caf0 : between c a f0) (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|) (hang_bac : ∠ b:a:c = ∟)
    (hah_af : |(a─h)| = |(a─f)|) (haf_fg : |(f─g)| = |(a─f)|)
    (hang_fgh : ∠ f:g:h = ∟) (hang_fah : ∠ f:a:h = ∟)
    (hGHAC : ¬GH.intersectsLine AC) (hAHFG : ¬AH.intersectsLine FG)
    (hhoff : ¬h.onLine AC) :
    Triangle.area △ f:g:h + Triangle.area △ f:a:h = |(a─h)| * |(a─h)| := by
  -- f ≠ a (a strictly between c and f), so f is off AH (AC ∩ AH = a) ⟹ FG ≠ AH.
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_apply (helper_2_11_step8_pyth a b c e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)))
  have step9_eaf : between e a f := by euclid_apply (helper_2_11_step9_eaf a b c e f f0 AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)))
  have hcaf : between c a f := by euclid_finish
  have hfa : f ≠ a := by euclid_finish
  have hah : a ≠ h := by euclid_finish
  have hfnAH : ¬f.onLine AH := offLine_of_two_points f a h AC AH hfAC haAC hfa haAH hhAH hhoff
  have hFGneAH : FG ≠ AH := line_ne_of_offLine f FG AH hfFG hfnAH
  -- the square FGHA is a right-angled parallelogram.
  have step22_par : formParallelogram f a g h AC GH FG AH := by euclid_apply (helper_2_11_step22_par f a g h AC GH FG AH (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine FG; assumption)) (by euclid_assumption "" (show FG ≠ AH; assumption)) (by euclid_assumption "" (show a ≠ h; assumption)))
  -- rectangle_area: △f:g:h + △f:a:h = |f-a|*|f-g|; both sides = |a-h| (square FGHA).
  obtain ⟨h1, _⟩ := rectangle_area f a g h AC GH FG AH ⟨step22_par, hang_fgh⟩
  have hfa_ah : |(f─a)| = |(a─h)| := by rw [segment_symmetric f a]; exact hah_af.symm
  have hfg_ah : |(f─g)| = |(a─h)| := haf_fg.trans hah_af.symm
  rw [hfa_ah, hfg_ah] at h1
  exact h1

end Elements.Book2
