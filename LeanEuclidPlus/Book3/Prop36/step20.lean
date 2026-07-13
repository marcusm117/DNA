import SystemE
import Book3.Prop36.step17_haf
import Book3.Prop36.step17_hcf
import Book3.Prop36.step20_hbet
import Book3.Prop36.step20_r6
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step20 (a c d e f : Point) (ABC : Circle) (DA : Line)
    (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC) (he_centre : e.isCentre ABC)
    (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
    (hbetdca : between d c a)
    (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
    (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
    (hlen : |(a─f)| = |(f─c)|) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  have hc_DA : c.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hne_DA : ¬ e.onLine DA := by euclid_finish
  have step17_haf : a ≠ f := by euclid_apply (helper_3_36_step17_haf a c e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have step17_hcf : c ≠ f := by euclid_apply (helper_3_36_step17_hcf a c e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have step20_hbet : between a f c := by euclid_apply (helper_3_36_step20_hbet a c f DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show a ≠ f; assumption)) (by euclid_assumption "" (show c ≠ f; assumption)))
  have step20_r6 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by euclid_apply (helper_3_36_step20_r6 a c d f DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show between a f c; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)))
  exact step20_r6

end Elements.Book3
