import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step24_oqac (a c o q : Point) (AB AE CH OP : Line)
    (h_a_ab : a.onLine AB) (h_c_ab : c.onLine AB)
    (h_a_ae : a.onLine AE) (h_o_ae : o.onLine AE)
    (h_c_ch : c.onLine CH) (h_q_ch : q.onLine CH)
    (h_q_op : q.onLine OP) (h_o_op : o.onLine OP)
    (h_acqo : formParallelogram a c o q AB OP AE CH) :
    |(o─q)| = |(a─c)| := by
  euclid_apply (line_from_points c o) as CO
  euclid_apply (Elements.Book1.proposition_34 a c o q AB OP AE CH CO)
  euclid_finish

end Elements.Book2
