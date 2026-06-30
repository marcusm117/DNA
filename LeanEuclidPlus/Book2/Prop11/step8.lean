import SystemE
import Book2.Prop11.step8_bisect
import Book2.Prop11.step8_pyth
import Book2.Prop11.step8_eb
import Book2.Prop11.step8_ahb_mag
import Book2.Prop11.step8_ahb
import Book2.Prop11.step8_golden
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step8
    (a b c e f f0 g h x : Point) (AB AC AH GH CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hbet_aec : between a e c)
    (hae_ec : |(a─e)| = |(e─c)|)
    (hac_ab : |(a─c)| = |(a─b)|)
    (hang_bac : ∠ b:a:c = ∟)
    (hbet_caf0 : between c a f0)
    (hbet_eff0 : between e f f0)
    (hef_be : |(e─f)| = |(b─e)|)
    (hah_af : |(a─h)| = |(a─f)|)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hang_fah : ∠ f:a:h = ∟)
    (hxoff : ¬ x.onLine AC) (hboff : ¬ b.onLine AC) (hhoff : ¬ h.onLine AC)
    (hxnsb : ¬ x.sameSide b AC) (hhnsx : ¬ h.sameSide x AC) :
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| := by
  have step8_bisect : |(a─b)| = |(a─e)| + |(a─e)| := by euclid_apply (helper_2_11_step8_bisect a b c e (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)))
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_apply (helper_2_11_step8_pyth a b c e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)))
  have step8_eb : |(e─b)| = |(a─e)| + |(a─f)| := by euclid_apply (helper_2_11_step8_eb a b c e f f0 AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)))
  have step8_ahb_mag : |(a─f)| < |(a─b)| := by euclid_apply (helper_2_11_step8_ahb_mag a b e f (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a─e)| + |(a─e)|; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)) (by euclid_assumption "" (show |(e─b)| = |(a─e)| + |(a─f)|; assumption)))
  have step8_ahb : |(a─b)| = |(a─h)| + |(b─h)| := by euclid_apply (helper_2_11_step8_ahb a b c e f f0 g h x AB AC AH GH CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(a─f)| < |(a─b)|; assumption)) (by euclid_assumption "" (show ¬ x.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show ¬ h.onLine AC; assumption)) (by euclid_assumption "" (show ¬ x.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬ h.sameSide x AC; assumption)))
  have step8_golden : |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| := by euclid_apply (helper_2_11_step8_golden a b e f h (by euclid_assumption "" (show |(a─b)| = |(a─e)| + |(a─e)|; assumption)) (by euclid_assumption "" (show |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)|; assumption)) (by euclid_assumption "" (show |(e─b)| = |(a─e)| + |(a─f)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a─h)| + |(b─h)|; assumption)))
  exact step8_golden

end Elements.Book2
