import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- 2.2.5: AF is the rectangle contained by BA and AC. AF (= ACFD) is contained by DA and AC,
   and AD = AB. Sub-nodes: step5_par (the parallelogram a c d f), step5_area (the rectangle_area
   identity △a:d:f + △a:c:f = |a─c|*|a─d|). Then |a─d| = |a─b| = |b─a| gives |b─a|*|a─c|. -/
theorem helper_2_2_step5 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (had : |(a─d)| = |(a─b)|) (hade : ∠ a:d:e = ∟) (hbad : ∠ b:a:d = ∟)
    (heb : e ≠ b) (hdsaBE : d.sameSide a BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) :
    Triangle.area △ a:c:f + Triangle.area △ a:d:f = |(b─a)| * |(a─c)| := by
  euclid_intros
  have step5_sameside : a.sameSide d CF := by sorry
  have step5_adne : a ≠ d := by sorry
  have step5_dene : DE ≠ AB := by sorry
  have step5_cf : c ≠ f := by sorry
  have step5_par : formParallelogram a c d f AB DE AD CF := by sorry
  have step3_dfe : between d f e := by sorry
  have step5_adf : ∠ a:d:f = ∟ := by sorry
  have step5_area : Triangle.area △ a:d:f + Triangle.area △ a:c:f = |(a─c)| * |(a─d)| := by sorry
  have hba : |(a─d)| = |(b─a)| := by euclid_finish
  have hprod : |(b─a)| * |(a─c)| = |(a─c)| * |(a─d)| := by rw [hba]; ring
  rw [hprod, ← step5_area]
  euclid_finish

end Elements.Book2
