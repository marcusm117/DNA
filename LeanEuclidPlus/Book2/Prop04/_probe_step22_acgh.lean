import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.22 sub: ACGH is a parallelogram, formParallelogram a c h g AB HK AD CF (a,c on AB; h,g on
   HK ∥ AB; a,h on AD; c,g on CF ∥ AD). proposition_34' then gives |a─c| = |h─g| and |a─h| = |c─g|.
   The sameSide a h CF comes from a,h both on AD ∥ CF (step22_ahcf); line distinctness from the
   off-line points c∉AD (step5_cnad), g∉AB (step9_gnab). -/
theorem helper_2_4_step22_acgh (a c g h : Point) (AB HK AD CF : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hhHK : h.onLine HK) (hgHK : g.onLine HK)
    (haAD : a.onLine AD) (hhAD : h.onLine AD)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADCF : ¬(AD.intersectsLine CF))
    (hahcf : a.sameSide h CF) (hcg : c ≠ g) :
    |(a─c)| = |(h─g)| ∧ |(a─h)| = |(c─g)| := by
  euclid_intros
  euclid_finish

end Elements.Book2
