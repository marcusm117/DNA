import SystemE
import Book3.Prop03.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- III.3: the perpendicular EF through the centre bisects the chord AB.
theorem helper_3_14_step4
    (a b e f : Point) (ABDC : Circle) (AB EF : Line)
    (ha : a.onCircle ABDC) (hb : b.onCircle ABDC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab_ne : a ≠ b)
    (hcen : e.isCentre ABDC)
    (hfAB : f.onLine AB) (hafb : between a f b) (hef : e ≠ f)
    (hassump1 : e.onLine EF ∧ f.onLine EF ∧ ∠ a:f:e = ∟) :
    |(a─f)| = |(f─b)| := by
  obtain ⟨heEF, hfEF, hfangle⟩ := hassump1
  have h_e_off : ¬ e.onLine AB := by euclid_finish
  euclid_apply (proposition_3 a b e f ABDC AB EF)
  euclid_finish

end Elements.Book3
