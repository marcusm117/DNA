import SystemE
import Book3.Prop33.step3_pos
import Book3.Prop33.step3_neg
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠d:a:e = ∟ : AD ⊥ AE at a and e ∈ line AE.  Split on whether e, e0 are on opposite rays.
theorem helper_3_33_step3
    (a d e e0 g : Point) (AD AE : Line)
    (hperp : ∠ d:a:e0 = ∟) (hadd : d ≠ a)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (heAE : e.onLine AE)
    (hega : between e g a) :
    ∠ d:a:e = ∟ := by
  have hdoffAE : ¬ d.onLine AE := by euclid_finish
  by_cases hbet : between e0 a e
  · have step3_pos : ∠ d:a:e = ∟ := by euclid_apply (helper_3_33_step3_pos a d e e0 AE (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ d.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show between e0 a e; assumption)))
    exact step3_pos
  · have step3_neg : ∠ d:a:e = ∟ := by euclid_apply (helper_3_33_step3_neg a d e e0 g AD AE (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ d.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show between e g a; assumption)) (by euclid_assumption "" (show ¬ between e0 a e; assumption)))
    exact step3_neg

end Elements.Book3
