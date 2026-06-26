import SystemE
import Book2.Prop03.step5_edf
import Book2.Prop03.step6_sameside
import Book2.Prop03.step6_cd
import Book2.Prop03.step6_fd
import Book2.Prop03.step6_par
import Book2.Prop03.step6_area
import Book2.Prop03.step6_haf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.3.6: AD is the rectangle contained by AC and CB, since DC = CB. The left rectangle ACDF (top
   A-C on AB, bottom F-D on DE, verticals AF and CD). Sub-nodes: step5_edf (between e d f, shared),
   step6_sameside (a.sameSide f CD), step6_par (the parallelogram a c f d), step6_area (the
   rectangle_area area identity △a:f:d + △a:d:c = |a─c|*|a─f|), step6_haf (|a─f| = |c─d|). Then
   |c─d| = |c─b| (square edge) gives the final |a─c|*|c─b|. -/
theorem helper_2_3_step6 (a b c d e f : Point) (AB DE CD BE AF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hfDE : f.onLine DE) (heDE : e.onLine DE) (hdDE : d.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hcd : |(c─d)| = |(c─b)|) (hde : |(d─e)| = |(c─b)|) (hbe : |(b─e)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcde : ∠ c:d:e = ∟) (hcbe : ∠ c:b:e = ∟) (hbed : ∠ b:e:d = ∟)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hAFCD : ¬(AF.intersectsLine CD)) :
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  euclid_intros
  have step5_edf : between e d f := by euclid_apply (helper_2_3_step5_edf a b c d e f AB DE CD BE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)))
  have step6_sameside : a.sameSide f CD := by euclid_apply (helper_2_3_step6_sameside a b c d e f AB DE CD BE AF (by euclid_assumption "" (show |(b─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between e d f; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)))
  have step6_cd : c ≠ d := by euclid_apply (helper_2_3_step6_cd a b c d (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)))
  have step6_fd : f ≠ d := by euclid_apply (helper_2_3_step6_fd d e f (by euclid_assumption "" (show between e d f; assumption)))
  have step6_par : formParallelogram a c f d AB DE AF CD := by euclid_apply (helper_2_3_step6_par a c d e f AB DE CD AF (by euclid_assumption "" (show between e d f; assumption)) (by euclid_assumption "" (show a.sameSide f CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show f ≠ d; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)))
  have step6_area : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(a─f)| := by euclid_apply (helper_2_3_step6_area a c d e f AB DE CD AF (by euclid_assumption "" (show formParallelogram a c f d AB DE AF CD; assumption)) (by euclid_assumption "" (show between e d f; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)))
  have step6_haf : |(a─f)| = |(c─d)| := by euclid_apply (helper_2_3_step6_haf a c d f AB DE CD AF (by euclid_assumption "" (show formParallelogram a c f d AB DE AF CD; assumption)))
  rw [step6_area, step6_haf, hcd]

end Elements.Book2
