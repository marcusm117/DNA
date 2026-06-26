import SystemE
import Book2.Prop02.step5_sameside
import Book2.Prop02.step5_adne
import Book2.Prop02.step5_dene
import Book2.Prop02.step5_cf
import Book2.Prop02.step5_par
import Book2.Prop02.step3_dfe
import Book2.Prop02.step5_adf
import Book2.Prop02.step5_area
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

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
  have step5_sameside : a.sameSide d CF := by euclid_apply (helper_2_2_step5_sameside a b c d e AB DE AD BE CF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show d.sameSide a BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step5_adne : a ≠ d := by euclid_apply (helper_2_2_step5_adne a b c d (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show between a c b; assumption)))
  have step5_dene : DE ≠ AB := by euclid_apply (helper_2_2_step5_dene a b c d AB DE AD (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)))
  have step5_cf : c ≠ f := by euclid_apply (helper_2_2_step5_cf c f AB DE (by euclid_assumption "" (show DE ≠ AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  have step5_par : formParallelogram a c d f AB DE AD CF := by euclid_apply (helper_2_2_step5_par a b c d e f AB DE AD CF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.sameSide d CF; assumption)) (by euclid_assumption "" (show c ≠ f; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step3_dfe : between d f e := by euclid_apply (helper_2_2_step3_dfe a b c d e f AB DE AD BE CF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show f.onLine CF; assumption)) (by euclid_assumption "" (show d.sameSide a BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have step5_adf : ∠ a:d:f = ∟ := by euclid_apply (helper_2_2_step5_adf a d e f AD DE (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)) (by euclid_assumption "" (show between d f e; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)))
  have step5_area : Triangle.area △ a:d:f + Triangle.area △ a:c:f = |(a─c)| * |(a─d)| := by euclid_apply (helper_2_2_step5_area a c d f AB DE AD CF (by euclid_assumption "" (show formParallelogram a c d f AB DE AD CF; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)))
  have hba : |(a─d)| = |(b─a)| := by euclid_finish
  have hprod : |(b─a)| * |(a─c)| = |(a─c)| * |(a─d)| := by rw [hba]; ring
  rw [hprod, ← step5_area]
  euclid_finish

end Elements.Book2
