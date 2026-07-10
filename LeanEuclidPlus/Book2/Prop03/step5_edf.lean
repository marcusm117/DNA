import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- sub-fact for 2.3.5 (and 2.3.6): the feet of the parallel verticals CD, BE, AF on the bottom
   line DE keep the top order between a c b, giving between e d f. AF ∥ CD given; AF ∥ BE via
   proposition_30. (Same derivation as step2's betweenness, isolated so it's proved once and
   downstream area steps get it cheaply.) -/
theorem helper_2_3_step5_edf (a b c d e f : Point) (AB DE CD BE AF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hfDE : f.onLine DE) (heDE : e.onLine DE) (hdDE : d.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hAFCD : ¬(AF.intersectsLine CD)) :
    between e d f := by
  euclid_intros
  euclid_apply (proposition_30 AF BE CD)
  euclid_finish

end Elements.Book2
