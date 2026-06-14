import SystemE
import Book2.Prop02.step6_cfbe
import Book2.Prop02.step6_sameside
import Book2.Prop02.step5_adne
import Book2.Prop02.step5_dene
import Book2.Prop02.step5_cf
import Book2.Prop02.step6_par
import Book2.Prop02.step3_dfe
import Book2.Prop02.step6_bef
import Book2.Prop02.step6_area
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

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
  have step6_cfbe : ¬(CF.intersectsLine BE) := by euclid_apply (helper_2_2_step6_cfbe a b c d e f AB DE AD BE CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step6_sameside : b.sameSide e CF := by euclid_apply (helper_2_2_step6_sameside a b c d e AB DE AD BE CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step5_adne : a ≠ d := by euclid_apply (helper_2_2_step5_adne a b c d (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step5_dene : DE ≠ AB := by euclid_apply (helper_2_2_step5_dene a b c d AB DE AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step5_cf : c ≠ f := by euclid_apply (helper_2_2_step5_cf c f AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step6_par : formParallelogram b c e f AB DE BE CF := by euclid_apply (helper_2_2_step6_par a b c d e f AB DE BE CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_dfe : between d f e := by euclid_apply (helper_2_2_step3_dfe a b c d e f AB DE AD BE CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step6_bef : ∠ b:e:f = ∟ := by euclid_apply (helper_2_2_step6_bef b d e f DE BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step6_area : Triangle.area △ c:b:e + Triangle.area △ c:f:e = |(b─c)| * |(b─e)| := by euclid_apply (helper_2_2_step6_area b c e f AB DE BE CF (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hprod : |(a─b)| * |(b─c)| = |(b─c)| * |(b─e)| := by rw [hbe]; ring
  rw [hprod]
  exact step6_area

end Elements.Book2
