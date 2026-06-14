import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.6: the right rectangle CBEF is a parallelogram (top C,B on AB; bottom F,E on DE;
   verticals CF and BE). b and e lie on BE which does not cross CF, placing them on the same side
   (step6_sameside); c ≠ f pins distinctness. -/
theorem helper_2_2_step6_par (a b c d e f : Point) (AB DE BE CF : Line)
    (hacb : between a c b) (hbse : b.sameSide e CF) (hcf : c ≠ f)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCFBE : ¬(CF.intersectsLine BE)) :
    formParallelogram b c e f AB DE BE CF := by
  euclid_intros
  euclid_finish

end Elements.Book2
