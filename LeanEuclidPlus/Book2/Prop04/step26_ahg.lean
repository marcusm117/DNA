import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.26 sub: ∠ a:h:g = ∟. AB (through a, b) ∥ HK (through h, g), cut by the transversal AD (through
   a, h). The co-interior angles sum to two right angles [Prop.~1.29] (proposition_29'''''):
   ∠ b:a:h + ∠ a:h:g = ∟ + ∟; and ∠ b:a:h = ∠ b:a:d = ∟ (h on ray a→d, square corner), so
   ∠ a:h:g = ∟. Needs b.sameSide g AD. -/
theorem helper_2_4_step26_ahg (a b d g h : Point) (AB AD HK : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK)
    (hahd : between a h d)
    (had : a ≠ d) (hab : a ≠ b) (hgh : g ≠ h) (hbsg : b.sameSide g AD)
    (hHKAB : ¬(HK.intersectsLine AB))
    (hbad : ∠ b:a:d = ∟) :
    ∠ a:h:g = ∟ := by
  euclid_intros
  euclid_apply (proposition_29''''' b g a h AB HK AD)
  euclid_finish

end Elements.Book2
