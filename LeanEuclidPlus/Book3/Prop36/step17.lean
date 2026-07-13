import SystemE
import Book3.Prop03.Main
import Book3.Prop36.step17_haf
import Book3.Prop36.step17_hcf
import Book3.Prop36.step17_finside
import Book3.Prop36.step17_hbet
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (hf_EF : f.onLine EF) (hbetdca : between d c a) (hef_ne : e ≠ f)
  (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : |(a─f)| = |(f─c)| := by
  have hc_DA : c.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hne_DA : ¬ e.onLine DA := hassump1.2.2.1
  have he_centre : e.isCentre ABC := hassump1.1
  have step17_haf : a ≠ f := by euclid_apply (helper_3_36_step17_haf a c e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have step17_hcf : c ≠ f := by euclid_apply (helper_3_36_step17_hcf a c e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have h1 : ∠ a:f:e = ∟ := hperp a ha_DA step17_haf
  have h2 : ∠ c:f:e = ∟ := hperp c hc_DA step17_hcf
  have step17_finside : f.insideCircle ABC := by euclid_apply (helper_3_36_step17_finside a e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show a ≠ f; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)))
  have step17_hbet : between a f c := by euclid_apply (helper_3_36_step17_hbet a c f ABC DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.insideCircle ABC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)))
  euclid_apply (proposition_3 a c e f ABC DA EF)
  euclid_finish

end Elements.Book3
