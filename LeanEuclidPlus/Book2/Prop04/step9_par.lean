import SystemE
import Book2.Prop04.step9_cnbe
import Book2.Prop04.step9_gnab
import Book2.Prop04.step9_cfbe
import Book2.Prop04.step9_csg
import Book2.Prop04.step9_bk
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.9/2.4.10 shared: CGKB is a parallelogram, formParallelogram c b g k AB HK CF BE. Sides: c,b on
   the base AB; g,k on HK (∥ AB); c,g on the vertical CF; b,k on the right side BE. From the root
   off-line facts c ∉ AD (c is the interior cut, off the left side) and a ∉ BE (a is off the right
   side), the line distinctness AD≠CF, CF≠BE, BE≠AD follow; then CF ∥ BE (step9_cfbe via Prop.~1.30),
   c.sameSide g BE (step9_csg) and b ≠ k (step9_bk) complete the parallelogram. -/
theorem helper_2_4_step9_par (a b c d e g k : Point) (AB CF AD BE HK BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD))
    (hcnAD : ¬(c.onLine AD)) (hanBE : ¬(a.onLine BE)) (hdnAB : ¬(d.onLine AB))
    (hbg : b ≠ g)
    (hab : a ≠ b) :
    formParallelogram c b g k AB HK CF BE := by
  euclid_intros
  -- line distinctness from the root off-line points
  have hADCF : AD ≠ CF := fun h => hcnAD (h ▸ hcCF)
  have hBEAD : BE ≠ AD := fun h => hanBE (h ▸ haAD)
  -- c ∉ BE and g ∉ AB (off-line via the base/right-side incidences)
  have step9_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_4_step9_cnbe a b c AB BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hCFBE : CF ≠ BE := fun h => step9_cnbe (h ▸ hcCF)
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- CF ∥ BE, c.sameSide g BE, b ≠ k complete the parallelogram
  have step9_cfbe : ¬(CF.intersectsLine BE) := by euclid_apply (helper_2_4_step9_cfbe CF AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_csg : c.sameSide g BE := by euclid_apply (helper_2_4_step9_csg c g CF BE (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_bk : b ≠ k := by euclid_apply (helper_2_4_step9_bk b g k AB HK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_finish

end Elements.Book2
