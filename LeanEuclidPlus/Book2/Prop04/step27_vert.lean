import SystemE

namespace Elements.Book2

-- 2.4.27 (leaf): vertical cut of the square ADEB by CF at c (on AB, between a,b) and f (on DE,
-- between d,e). sum_parallelograms_area splits ADEB into the left strip (△d:a:c+△d:c:f) and the
-- right strip (△f:c:b+△f:b:e), summing to △d:a:b+△d:b:e. Goal in exact emission form.
set_option systemE.solverTime 30 in
theorem helper_2_step27_vert (a b c d e f : Point) (AB DE AD BE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdAD : d.onLine AD) (haAD : a.onLine AD) (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hcAB : c.onLine AB) (hacb : between a c b)
    (hfDE : f.onLine DE) (hdfe : between d f e)
    (hdaBE : d.sameSide a BE) (heb : e ≠ b) :
    Triangle.area △ d:a:c + Triangle.area △ d:c:f + Triangle.area △ f:c:b + Triangle.area △ f:b:e =
    Triangle.area △ d:a:b + Triangle.area △ d:b:e := by
  euclid_intros
  euclid_apply (sum_parallelograms_area d e a b f c DE AB AD BE)
  euclid_finish

end Elements.Book2
