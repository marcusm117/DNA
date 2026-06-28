import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- top2: top-rest rectangle (q-p-h-f) cut by BL (r on q-p, l on h-f). -/
theorem helper_2_8_step26_top2 (q r p h l f : Point)
    (CH DF EF OP BL : Line)
    (h_q_ch : q.onLine CH) (h_h_ch : h.onLine CH)
    (h_r_bl : r.onLine BL) (h_l_bl : l.onLine BL)
    (h_d_df : p.onLine DF) (h_f_df : f.onLine DF)
    (h_h_ef : h.onLine EF) (h_l_ef : l.onLine EF) (h_f_ef : f.onLine EF)
    (h_q_op : q.onLine OP) (h_r_op : r.onLine OP) (h_p_op : p.onLine OP)
    (h_qrp : between q r p) (h_hlf : between h l f)
    (h_top2par : formParallelogram q p h f OP EF CH DF) :
    Triangle.area △ q:h:f + Triangle.area △ q:f:p =
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
        (Triangle.area △ r:p:f + Triangle.area △ r:f:l) := by
  euclid_apply (sum_parallelograms_area q p h f r l OP EF CH DF)
  euclid_finish

end Elements.Book2
