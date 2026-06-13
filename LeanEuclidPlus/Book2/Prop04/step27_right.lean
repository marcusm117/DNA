import SystemE

namespace Elements.Book2

-- 2.4.27 (leaf): horizontal cut of the RIGHT strip, exact sum_parallelograms_area emission form.
set_option systemE.solverTime 30 in
theorem helper_2_step27_right (b c e f g k : Point) (AB DE CF BE : Line)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF) (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB) (hfDE : f.onLine DE) (heDE : e.onLine DE)
    (hgCF : g.onLine CF) (hkBE : k.onLine BE)
    (hcgf : between c g f) (hbke : between b k e)
    (hcDEb : c.sameSide b DE) (hfe : f ≠ e)
    (hCFBE : ¬(CF.intersectsLine BE)) (hABDE : ¬(AB.intersectsLine DE)) :
    Triangle.area △ c:b:k + Triangle.area △ c:k:g + Triangle.area △ g:k:e + Triangle.area △ g:e:f =
    Triangle.area △ f:c:b + Triangle.area △ f:b:e := by
  euclid_intros
  euclid_apply (sum_parallelograms_area c f b e g k CF BE AB DE)
  euclid_apply (parallelogram_area c f b e CF BE AB DE)
  euclid_finish

end Elements.Book2
