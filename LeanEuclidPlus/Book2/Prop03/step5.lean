import SystemE
import Book.Prop30

namespace Elements.Book2

open Elements.Book1

/- 2.3.5: AE is the rectangle contained by AB and BC. AE is contained by AB and BE, and BE = BC.
   With between e d f (step5_edf), the corner f of the whole rectangle b a e f sits so ∠b:e:f =
   ∠b:e:d = ∟; rectangle_area gives △b:a:e + △b:f:e = |b─a|*|b─e|, and |b─e| = |c─b| = |b─c|. -/
set_option systemE.solverTime 30 in
theorem helper_2_step5 (a b c d e f : Point) (AB DE CD BE AF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hfDE : f.onLine DE) (heDE : e.onLine DE) (hdDE : d.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hbe : |(b─e)| = |(c─b)|) (hbed : ∠ b:e:d = ∟)
    (hdscBE : d.sameSide c BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hCDBE : ¬(CD.intersectsLine BE))
    (hAFCD : ¬(AF.intersectsLine CD)) (heb : e ≠ b) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  euclid_intros
  have step5_edf : between e d f := by sorry
  euclid_apply (proposition_30 AF BE CD)
  euclid_apply (rectangle_area b a e f AB DE BE AF)
  have hba : |(a─b)| = |(b─a)| := by euclid_finish
  have hbc : |(b─c)| = |(b─e)| := by euclid_finish
  have hprod : |(a─b)| * |(b─c)| = |(b─a)| * |(b─e)| := by rw [hba, hbc]
  rw [hprod]
  euclid_finish

end Elements.Book2
