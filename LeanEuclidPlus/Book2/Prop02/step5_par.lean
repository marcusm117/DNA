import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.5: the left rectangle ACFD is a parallelogram (top A,C on AB; bottom D,F on DE;
   verticals AD and CF). a and d lie on AD which does not cross CF, placing them on the same side;
   between a c b and the layout pin the rest. -/
theorem helper_2_2_step5_par (a b c d e f : Point) (AB DE AD CF : Line)
    (hacb : between a c b) (hasd : a.sameSide d CF) (hcf : c ≠ f)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCFAD : ¬(CF.intersectsLine AD)) :
    formParallelogram a c d f AB DE AD CF := by
  euclid_intros
  euclid_finish

end Elements.Book2
