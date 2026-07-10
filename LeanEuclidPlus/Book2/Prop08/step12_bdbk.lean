import SystemE
import Book1Variants.Prop05
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step12_bdbk (a b d e k : Point) (AB AE BL ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_abd : between a b d)
    (h_d_ab : d.onLine AB) (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_bl_ae : ¬(BL.intersectsLine AE)) (h_dae : ∠ d:a:e = ∟) :
    |(b─d)| = |(b─k)| := by
  have htri_ade : formTriangle a d e AB ED AE := by
    euclid_finish
  euclid_apply (Elements.Book1.proposition_5' a d e AB ED AE)
  have htri_bdk : formTriangle b d k AB ED BL := by
    euclid_finish
  have hang : ∠ b:d:k = ∠ b:k:d := by
    euclid_finish
  euclid_apply (Elements.Book1.proposition_6 b d k AB ED BL)
  euclid_finish

end Elements.Book2
