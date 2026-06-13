import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.3.2: ED drawn through to F. f = AF ∩ DE lies on DE (immediate); the feet d, e, f of the
   parallel verticals CD, BE, AF on the bottom line DE preserve the order between a c b of their
   tops a, c, b, giving between e d f. AF ∥ CD is given; AF ∥ BE follows by proposition_30 from
   AF ∥ CD and CD ∥ BE. The sameSide / non-intersection atoms (the square's) pin the order. -/
theorem helper_2_3_step2 (a b c d e f : Point) (AB DE CD BE AF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (haAF : a.onLine AF) (hcCD : c.onLine CD) (hbBE : b.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hdCD : d.onLine CD) (heBE : e.onLine BE)
    (hfAF : f.onLine AF) (hfDE : f.onLine DE)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hAFCD : ¬(AF.intersectsLine CD)) :
    f.onLine DE ∧ between e d f := by
  euclid_intros
  euclid_apply (proposition_30 AF BE CD)
  euclid_finish

end Elements.Book2
