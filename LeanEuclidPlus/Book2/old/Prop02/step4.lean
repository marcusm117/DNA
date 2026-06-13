import SystemE

namespace Elements.Book2

/- 2.2.4: AF = rect(BA,AC). rectangle_area on the sub-rectangle a,c,f,d; |a─d| = |a─b| = |b─a|. -/
set_option systemE.solverTime 30 in
theorem helper_2_2_step4 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (had : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (hcAB : c.onLine AB) (hacb : between a c b)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hfDE : f.onLine DE) (hfCF : f.onLine CF) (hdfe : between d f e) :
    Triangle.area △ d:a:c + Triangle.area △ d:c:f = |(b─a)| * |(a─c)| := by
  euclid_intros
  euclid_apply (rectangle_area a c d f AB DE AD CF)
  have hba : |(b─a)| = |(a─d)| := by euclid_finish
  have hprod : |(b─a)| * |(a─c)| = |(a─c)| * |(a─d)| := by rw [hba]; ring
  rw [hprod]
  euclid_finish

end Elements.Book2
