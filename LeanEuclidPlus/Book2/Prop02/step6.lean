import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- 2.2.6: CE is the rectangle contained by AB and BC, since BE = AB. The right rectangle CBEF (top
   C-B on AB, bottom F-E on DE, verticals CF and BE). Sub-nodes mirror step5: step6_sameside
   (b.sameSide e CF), step6_cf (c ≠ f, shared), step6_par (the parallelogram b c e f), step6_bef
   (∠b:e:f = ∟ via the foot f between d,e), step6_area (rectangle_area: △c:b:e + △c:f:e =
   |b─c|*|b─e|). Then |b─e| = |a─b| gives |a─b|*|b─c|. -/
theorem helper_2_2_step6 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hbe : |(b─e)| = |(a─b)|) (hbed : ∠ b:e:d = ∟)
    (had : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (heb : e ≠ b) (hdsaBE : d.sameSide a BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) :
    Triangle.area △ c:b:e + Triangle.area △ c:f:e = |(a─b)| * |(b─c)| := by
  euclid_intros
  have step6_cfbe : ¬(CF.intersectsLine BE) := by sorry
  have step6_sameside : b.sameSide e CF := by sorry
  have step5_adne : a ≠ d := by sorry
  have step5_dene : DE ≠ AB := by sorry
  have step5_cf : c ≠ f := by sorry
  have step6_par : formParallelogram b c e f AB DE BE CF := by sorry
  have step3_dfe : between d f e := by sorry
  have step6_bef : ∠ b:e:f = ∟ := by sorry
  have step6_area : Triangle.area △ c:b:e + Triangle.area △ c:f:e = |(b─c)| * |(b─e)| := by sorry
  have hprod : |(a─b)| * |(b─c)| = |(b─c)| * |(b─e)| := by rw [hbe]; ring
  rw [hprod]
  exact step6_area

end Elements.Book2
