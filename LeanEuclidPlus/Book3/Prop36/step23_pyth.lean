import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step23_pyth (c e f : Point) (ABC : Circle) (DA : Line)
    (hassump1 : ∠ e:f:c = ∟)
    (he_centre : e.isCentre ABC) (hc_circ : c.onCircle ABC)
    (hf_DA : f.onLine DA) (hc_DA : c.onLine DA) (hne_DA : ¬ e.onLine DA)
    (hcf : c ≠ f) :
    |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points e c) as EC
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_47 f e c FE EC FC)
  euclid_finish

end Elements.Book3
