import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- mid2: middle-rest rectangle (g-n-q-p) cut by BL (k on g-n, r on q-p). -/
theorem helper_2_8_step26_mid2 (g k n q r p : Point)
    (CH DF MN OP BL : Line)
    (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH)
    (h_b_bl : k.onLine BL) (h_r_bl : r.onLine BL)
    (h_d_df : n.onLine DF) (h_p_df : p.onLine DF)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP) (h_p_op : p.onLine OP)
    (h_gkn : between g k n) (h_qrp : between q r p)
    (h_mid2par : formParallelogram g n q p MN OP CH DF) :
    Triangle.area △ g:q:p + Triangle.area △ g:p:n =
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
        (Triangle.area △ k:n:p + Triangle.area △ k:p:r) := by
  euclid_apply (sum_parallelograms_area g n q p k r MN OP CH DF)
  euclid_finish

end Elements.Book2
