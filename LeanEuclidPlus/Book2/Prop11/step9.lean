import SystemE
import Book2.Prop06.Main
import Book2.Prop11.step8_pyth
import Book2.Prop11.step9_eaf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step9
    (a b c e f f0 : Point) (AB AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hbet_aec : between a e c)
    (hae_ec : |(a─e)| = |(e─c)|)
    (hang_bac : ∠ b:a:c = ∟)
    (hbet_caf0 : between c a f0)
    (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|) :
    |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─f)| * |(e─f)| := by
  -- Pythagoras on right triangle a-e-b (reuses step8_pyth).
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_apply (helper_2_11_step8_pyth a b c e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)))
  -- f lies beyond a on ray e→f0, so a is between e and f (magnitude argument).
  have step9_eaf : between e a f := by euclid_apply (helper_2_11_step9_eaf a b c e f f0 AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)))
  -- AC bisected at E, with AF added beyond A ⟹ II.6 (relabel a→c, b→a, c→e, d→f).
  euclid_apply (Elements.Book2.proposition_6 c a e f AC)
  euclid_finish

end Elements.Book2
