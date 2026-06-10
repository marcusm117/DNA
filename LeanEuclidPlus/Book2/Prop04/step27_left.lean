import SystemE

namespace Elements.Book2

-- 2.4.27 (sub): left strip ACFD splits by HK (at h on AD, g on CF) into AG (top) + HF (bottom).
-- ACFD is a parallelogram (a,c on AB-side? no: a,d on AD; c,f on CF; AD ∥ CF; a,c on AB; d,f on DE).
-- Orientation: corners a (top-left), c (top-right via AB... ) — use the parallelogram a c f d with
-- top AB-segment a c, verticals; split points h (between a,d) and g (between c,f).
set_option systemE.solverTime 30 in
theorem helper_2_step27_left (a c d f g h : Point) (AB DE AD CF HK : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdDE : d.onLine DE) (hfDE : f.onLine DE)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (hhAD : h.onLine AD) (hgCF : g.onLine CF)
    (hahd : between a h d) (hcgf : between c g f)
    (hADCF : ¬(AD.intersectsLine CF)) (hABDE : ¬(AB.intersectsLine DE)) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h
      + (Triangle.area △ h:g:f + Triangle.area △ h:f:d)
    = Triangle.area △ a:c:f + Triangle.area △ a:f:d := by
  euclid_intros
  euclid_apply (sum_parallelograms_area a c f d h g AB DE AD CF)
  euclid_finish

end Elements.Book2
