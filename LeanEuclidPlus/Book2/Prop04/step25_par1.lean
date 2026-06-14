import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.25 sub: CGKB as formParallelogram b k c g BE CF AB HK (b,k on BE; c,g on CF; b,c on AB;
   k,g on HK; b.sameSide c HK; BE ∥ CF; AB ∥ HK). sameSide b c HK (b,c on AB ∥ HK) + the
   non-intersections + k ≠ g supplied. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step25_par1 (b k c g : Point) (BE CF AB HK : Line)
    (hbBE : b.onLine BE) (hkBE : k.onLine BE)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hkHK : k.onLine HK) (hgHK : g.onLine HK)
    (hBECF : ¬(BE.intersectsLine CF)) (hABHK : ¬(AB.intersectsLine HK))
    (hbchk : b.sameSide c HK) (hkg : k ≠ g) :
    formParallelogram b k c g BE CF AB HK := by
  euclid_intros
  euclid_finish

end Elements.Book2
