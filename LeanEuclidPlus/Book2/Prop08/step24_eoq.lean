import SystemE
import Helpers.Angle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step24_eoq (a d e o q : Point) (AB AE OP : Line)
    (h_a_ab : a.onLine AB) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_q_op : q.onLine OP) (h_o_op : o.onLine OP)
    (h_op_ab : ¬(OP.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟)
    (h_aoe : between a o e) (h_qdae : q.sameSide d AE) :
    ∠ e:o:q = ∟ := by
  euclid_apply (Elements.corresponding_angle e d q a o OP AB AE)
  euclid_finish

end Elements.Book2
