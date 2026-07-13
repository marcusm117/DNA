import SystemE
import Book3.Prop36.step17_haf
import Book3.Prop36.step17_finside
import Book3.Prop36.step24_pyth
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24 (a c d e f : Point) (ABC : Circle) (DA : Line)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC) (he_centre : e.isCentre ABC)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (hbetdca : between d c a) (hef : e ≠ f)
  (hd_out : ¬ d.insideCircle ABC) (hd_noncirc : ¬ d.onCircle ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have hne_DA : ¬ e.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hc_DA : c.onLine DA := by euclid_finish
  have step17_haf : a ≠ f := by euclid_apply (helper_3_36_step17_haf a c e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have h1 : ∠ a:f:e = ∟ := hperp a ha_DA step17_haf
  have step17_finside : f.insideCircle ABC := by euclid_apply (helper_3_36_step17_finside a e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show a ≠ f; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)))
  have hdf : d ≠ f := by euclid_finish
  have hdfe : ∠ d:f:e = ∟ := hperp d hd_DA hdf
  have step24_pyth : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by euclid_apply (helper_3_36_step24_pyth d e f DA (by euclid_assumption "" (show ∠ d:f:e = ∟; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)))
  exact step24_pyth

end Elements.Book3
