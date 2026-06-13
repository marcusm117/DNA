import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.3.6: the left rectangle ACDF is a parallelogram (top A,C on AB; bottom F,D on DE;
   verticals AF and CD). Its only non-obvious conjunct, a.sameSide f CD, is supplied (step6_sameside);
   between e d f pins the bottom layout. -/
theorem helper_2_3_step6_par (a c d e f : Point) (AB DE CD AF : Line)
    (hedf : between e d f) (hasf : a.sameSide f CD)
    (hcd : c ≠ d) (hfd : f ≠ d)
    (haAB : a.onLine AB) (hcAB : c.onLine AB)
    (hfDE : f.onLine DE) (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hDEAB : ¬(DE.intersectsLine AB)) (hAFCD : ¬(AF.intersectsLine CD)) :
    formParallelogram a c f d AB DE AF CD := by
  euclid_intros
  euclid_finish

end Elements.Book2
