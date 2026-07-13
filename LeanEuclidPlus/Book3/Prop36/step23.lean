import SystemE
import Book3.Prop36.step17_hcf
import Book3.Prop36.step23_pyth
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23 (a c d e f : Point) (ABC : Circle) (DA : Line)
  (hassump1 : ∠ e:f:c = ∟)
  (he_centre : e.isCentre ABC) (hc_circ : c.onCircle ABC) (ha_circ : a.onCircle ABC)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (hbetdca : between d c a)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have hne_DA : ¬ e.onLine DA := by euclid_finish
  have hc_DA : c.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have step17_hcf : c ≠ f := by euclid_apply (helper_3_36_step17_hcf a c e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have step23_pyth : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by euclid_apply (helper_3_36_step23_pyth c e f ABC DA (by euclid_assumption "" (show ∠ e:f:c = ∟; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show c ≠ f; assumption)))
  exact step23_pyth

end Elements.Book3
