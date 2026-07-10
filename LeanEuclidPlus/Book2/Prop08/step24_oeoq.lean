import SystemE
import Book1Variants.Prop05
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step24_oeoq (a b d e o q : Point) (AB AE ED OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_q_ed : q.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_q_op : q.onLine OP) (h_o_op : o.onLine OP)
    (h_dae : ∠ d:a:e = ∟)
    (h_aoe : between a o e) (h_eqd : between e q d) (h_eoq : ∠ e:o:q = ∟) :
    |(o─e)| = |(o─q)| := by
  have htri_ade : formTriangle a d e AB ED AE := by
    euclid_finish
  euclid_apply (Elements.Book1.proposition_5' a d e AB ED AE)
  have htri_oeq : formTriangle o e q AE ED OP := by
    euclid_finish
  have h_eq_eq : ∠ o:e:q = ∠ o:q:e := by
    euclid_finish
  euclid_apply (Elements.Book1.proposition_6 o e q AE ED OP)
  euclid_finish

end Elements.Book2
