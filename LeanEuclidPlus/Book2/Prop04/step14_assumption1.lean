import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.14 assumption: ¬(CF.intersectsLine BE). CF ∥ AD (step5_assumption1) and
   AD ∥ BE (the square's opposite sides), so CF ∥ BE by transitivity [Prop.~1.30]. -/
theorem helper_2_4_step14_assumption1 (a b c d e g : Point) (AB CF AD BE : Line)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hacb : between a c b)
    (hCFAD : ¬(CF.intersectsLine AD))
    (hADBE : ¬(AD.intersectsLine BE))
    (heb : e ≠ b) :
    ¬(CF.intersectsLine BE) := by
  euclid_intros
  have hcAB : c.onLine AB := by euclid_apply (between_same_line_in a c b AB); euclid_finish
  have hbc : b ≠ c := by euclid_finish
  -- distinctness from off-line witnesses
  have hcAD : ¬(c.onLine AD) := by euclid_finish
  have hasBE : ¬(a.onLine BE) := by euclid_finish
  have hcBE : ¬(c.onLine BE) := by euclid_finish
  have hADCF : AD ≠ CF := fun h => hcAD (h ▸ hcCF)
  have hBEAD : BE ≠ AD := fun h => hasBE (h ▸ haAD)
  have hCFBE : CF ≠ BE := fun h => hcBE (h ▸ hcCF)
  euclid_apply (proposition_30 CF BE AD)
  euclid_finish

end Elements.Book2
