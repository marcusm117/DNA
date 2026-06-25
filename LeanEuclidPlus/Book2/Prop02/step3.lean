import SystemE
import Book2.Prop02.step3_dfe
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.2.3: the square AE (the whole ADEB) = rectangle AF (ACFD) + rectangle CE (CBEF).
   The square d e a b (bottom D E, top A B, verticals AD, BE) is cut by the middle vertical
   CF at c (top, between a b) and f (bottom, between d e); sum_parallelograms_area gives the
   area split. The verticals AD ∥ BE come from the square (formParallelogram). -/
theorem helper_2_2_step3 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hdsaBE : d.sameSide a BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) (heb : e ≠ b) (hab : a ≠ b) :
    Triangle.area △ a:d:e + Triangle.area △ a:b:e =
      (Triangle.area △ a:c:f + Triangle.area △ a:d:f)
    + (Triangle.area △ c:b:e + Triangle.area △ c:f:e) := by
  euclid_intros
  have step3_dfe : between d f e := by euclid_apply (helper_2_2_step3_dfe a b c d e f AB DE AD BE CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_apply (sum_parallelograms_area d e a b f c DE AB AD BE)
  euclid_finish

end Elements.Book2
