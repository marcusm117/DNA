import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: ACGH is a parallelogram, formParallelogram a c h g AB HK AD CF (a,c on AB; h,g on HK;
   a,h on AD; c,g on CF; a.sameSide h CF; AB ∥ HK; AD ∥ CF). The sameSide a h CF (a,h on AD ∥ CF)
   and the non-intersections are supplied; line distinctness from off-line points. -/
theorem helper_2_4_step25_paracgh (a c h g : Point) (AB HK AD CF : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hhHK : h.onLine HK) (hgHK : g.onLine HK)
    (haAD : a.onLine AD) (hhAD : h.onLine AD)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADCF : ¬(AD.intersectsLine CF))
    (hahcf : a.sameSide h CF) (hcg : c ≠ g) :
    formParallelogram a c h g AB HK AD CF := by
  euclid_intros
  euclid_finish

end Elements.Book2
