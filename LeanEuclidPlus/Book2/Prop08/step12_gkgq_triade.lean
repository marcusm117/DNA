import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step12_gkgq_triade (a b d e : Point) (AB AE ED : Line)
    (h_a_ab : a.onLine AB) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_dae : ∠ d:a:e = ∟) :
    formTriangle a d e AB ED AE := by
  euclid_finish

end Elements.Book2
