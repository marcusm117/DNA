import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.3.7: the square CDEB as formParallelogram c b d e AB DE CD BE (top C-B on AB,
   bottom D-E on DE, verticals CD and BE), repackaged from the proposition_46 construction atoms.
   Minimal context so it is fast. -/
theorem helper_2_3_step7_par (a b c d e : Point) (AB DE CD BE : Line)
    (hacb : between a c b) (hbelen : |(b─e)| = |(c─b)|)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE)) :
    formParallelogram c b d e AB DE CD BE := by
  euclid_intros
  have hcb : c ≠ b := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  euclid_finish

end Elements.Book2
