import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_hcf (a c e f : Point) (ABC : Circle) (DA : Line)
    (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC) (he_centre : e.isCentre ABC)
    (ha_DA : a.onLine DA) (hc_DA : c.onLine DA) (hf_DA : f.onLine DA)
    (hne_DA : ¬ e.onLine DA) (hac : a ≠ c)
    (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟) :
    c ≠ f := by
  intro heq
  subst heq
  have hang : ∠ a:c:e = ∟ := hperp a ha_DA hac
  euclid_apply (line_from_points c a) as CA
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points c e) as CE
  euclid_apply (proposition_47 c a e CA AE CE)
  euclid_finish

end Elements.Book3
