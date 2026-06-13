import SystemE

namespace Elements.Book2

-- 2.4.27 (leaf): horizontal cut of the LEFT strip, exact sum_parallelograms_area emission form.
set_option systemE.solverTime 30 in
theorem helper_2_step27_left (a c d f g h : Point) (AB DE AD CF : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdDE : d.onLine DE) (hfDE : f.onLine DE)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hhAD : h.onLine AD) (hgCF : g.onLine CF)
    (hahd : between a h d) (hcgf : between c g f)
    (haDEc : a.sameSide c DE) (hdf : d ≠ f)
    (hADCF : ¬(AD.intersectsLine CF)) (hABDE : ¬(AB.intersectsLine DE)) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h + Triangle.area △ h:g:f + Triangle.area △ h:f:d =
    Triangle.area △ d:a:c + Triangle.area △ d:c:f := by
  euclid_intros
  euclid_apply (sum_parallelograms_area a d c f h g AD CF AB DE)
  euclid_apply (parallelogram_area a d c f AD CF AB DE)
  euclid_finish

end Elements.Book2
