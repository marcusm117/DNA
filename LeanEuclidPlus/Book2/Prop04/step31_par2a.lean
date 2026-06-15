import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.31 sub: left rectangle ADFC as formParallelogram a d c f AD CF AB DE (a,d on AD; c,f on CF;
   a,c on AB; d,f on DE; a.sameSide c DE; AD ∥ CF; AB ∥ DE). sameSide a c DE + non-intersections +
   d ≠ f supplied. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step31_par2a (a d c f : Point) (AD CF AB DE : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (hfDE : f.onLine DE)
    (hCFAD : ¬(CF.intersectsLine AD)) (hABDE : ¬(AB.intersectsLine DE))
    (hacde : a.sameSide c DE) (hdf : d ≠ f) :
    formParallelogram a d c f AD CF AB DE := by
  euclid_intros
  euclid_finish

end Elements.Book2
