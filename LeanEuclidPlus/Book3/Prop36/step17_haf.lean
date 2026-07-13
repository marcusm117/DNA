import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_haf (a c e f : Point) (ABC : Circle) (DA : Line)
    (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC) (he_centre : e.isCentre ABC)
    (ha_DA : a.onLine DA) (hc_DA : c.onLine DA) (hf_DA : f.onLine DA)
    (hne_DA : ¬ e.onLine DA) (hac : a ≠ c)
    (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟) :
    a ≠ f := by
  intro heq
  subst heq
  have hang : ∠ c:a:e = ∟ := hperp c hc_DA (Ne.symm hac)
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points c e) as CE
  euclid_apply (line_from_points a e) as AE
  euclid_apply (proposition_47 a c e AC CE AE)
  euclid_finish

end Elements.Book3
