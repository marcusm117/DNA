import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- mid1: middle strip (m-n-o-p) cut by CH (g on m-n, q on o-p). -/
theorem helper_2_8_step26_mid1 (m n o p g q : Point)
    (AE CH DF MN OP : Line)
    (h_m_ae : m.onLine AE) (h_o_ae : o.onLine AE)
    (h_d_df : n.onLine DF) (h_p_df : p.onLine DF)
    (h_c_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_g_mn : g.onLine MN) (h_m_mn : m.onLine MN) (h_n_mn : n.onLine MN)
    (h_o_op : o.onLine OP) (h_q_op : q.onLine OP) (h_p_op : p.onLine OP)
    (h_mgn : between m g n) (h_oqp : between o q p)
    (h_mid1par : formParallelogram m n o p MN OP AE DF) :
    Triangle.area △ m:n:p + Triangle.area △ m:p:o =
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
        (Triangle.area △ g:q:p + Triangle.area △ g:p:n) := by
  euclid_apply (sum_parallelograms_area m n o p g q MN OP AE DF)
  euclid_finish

end Elements.Book2
