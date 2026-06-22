import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4 sub: the right-half rectangle CBEN as formParallelogram c n b e CN BE AB DE (c,n on CN;
   b,e on BE; c,b on AB; n,e on DE; c.sameSide n ...; CN ∥ BE; AB ∥ DE). -/
theorem helper_2_7_step4_parCE (c n b e : Point) (CN BE AB DE : Line)
    (hcCN : c.onLine CN) (hnCN : n.onLine CN)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hnDE : n.onLine DE) (heDE : e.onLine DE)
    (hCNBE : ¬(CN.intersectsLine BE)) (hABDE : ¬(AB.intersectsLine DE))
    (hcsn : c.sameSide b DE) (hne : n ≠ e) :
    formParallelogram c n b e CN BE AB DE := by
  euclid_intros
  euclid_finish

end Elements.Book2
