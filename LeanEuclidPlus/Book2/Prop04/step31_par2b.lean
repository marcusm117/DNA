import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.31 sub: right rectangle CFEB as formParallelogram c f b e CF BE AB DE (c,f on CF; b,e on... )
   c,f on CF; b,e on BE; c,b on AB; f,e on DE; c.sameSide b DE; CF ∥ BE; AB ∥ DE. sameSide c b DE +
   non-intersections + f ≠ e supplied. -/
theorem helper_2_4_step31_par2b (c f b e : Point) (CF BE AB DE : Line)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hfDE : f.onLine DE) (heDE : e.onLine DE)
    (hCFBE : ¬(CF.intersectsLine BE)) (hABDE : ¬(AB.intersectsLine DE))
    (hcbde : c.sameSide b DE) (hfe : f ≠ e) :
    formParallelogram c f b e CF BE AB DE := by
  euclid_intros
  euclid_finish

end Elements.Book2
