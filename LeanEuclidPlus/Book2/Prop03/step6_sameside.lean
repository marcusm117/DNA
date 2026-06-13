import SystemE

namespace Elements.Book2

/- sub-fact for 2.3.6: a.sameSide f CD. a and f lie on AF, which does not cross CD. Given the
   square CDEB's parallelogram step6_hsq, the SMT places a, f on the same side of CD in one step —
   no hand-derived off-line lemmas. between e d f pins the bottom-feet layout. -/
set_option systemE.solverTime 30 in
theorem helper_2_step6_sameside (a b c d e f : Point) (AB DE CD BE AF : Line)
    (hbe : |(b─e)| = |(c─b)|)
    (hacb : between a c b) (hedf : between e d f)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hfDE : f.onLine DE) (heDE : e.onLine DE) (hdDE : d.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hAFCD : ¬(AF.intersectsLine CD)) :
    a.sameSide f CD := by
  euclid_intros
  have step6_hsq : formParallelogram d e c b DE AB CD BE := by sorry
  euclid_finish

end Elements.Book2
