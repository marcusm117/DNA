import SystemE

namespace Elements.Book2

/- sub-fact: the square CDEB's parallelogram, formParallelogram d e c b DE AB CD BE, repackaged
   from the atoms the proposition_46 construction left in context. Minimal context so it is fast. -/
set_option systemE.solverTime 30 in
theorem helper_2_step6_hsq (a b c d e : Point) (AB DE CD BE : Line)
    (hacb : between a c b) (hbelen : |(b─e)| = |(c─b)|)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE)) :
    formParallelogram d e c b DE AB CD BE := by
  euclid_intros
  have heb : e ≠ b := by euclid_finish
  euclid_finish

end Elements.Book2
