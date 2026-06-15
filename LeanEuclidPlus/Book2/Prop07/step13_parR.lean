import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: the right half CNEB as formParallelogram c n b e CN BE AB DE (c,n on CN; b,e on BE;
   c,b on AB; n,e on DE; c.sameSide b DE; CN ∥ BE; AB ∥ DE). -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step13_parR (c n b e : Point) (CN BE AB DE : Line)
    (hcCN : c.onLine CN) (hnCN : n.onLine CN)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hnDE : n.onLine DE) (heDE : e.onLine DE)
    (hCNBE : ¬(CN.intersectsLine BE)) (hABDE : ¬(AB.intersectsLine DE))
    (hcsb : c.sameSide b DE) (hne : n ≠ e) :
    formParallelogram c n b e CN BE AB DE := by
  euclid_intros
  euclid_finish

end Elements.Book2
