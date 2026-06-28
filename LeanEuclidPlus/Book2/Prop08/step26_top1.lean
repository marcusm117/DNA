import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- top1: top strip (o-p-e-f) cut by CH (q on o-p, h on e-f). -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_top1 (o q p e h f : Point)
    (AE CH DF EF OP : Line)
    (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_d_df : p.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ef : e.onLine EF) (h_h_ef : h.onLine EF) (h_f_ef : f.onLine EF)
    (h_q_ch : q.onLine CH) (h_h_ch : h.onLine CH)
    (h_o_op : o.onLine OP) (h_q_op : q.onLine OP) (h_p_op : p.onLine OP)
    (h_oqp : between o q p) (h_ehf : between e h f)
    (h_top1par : formParallelogram o p e f OP EF AE DF) :
    Triangle.area △ o:p:f + Triangle.area △ o:f:e =
      (Triangle.area △ o:q:h + Triangle.area △ o:h:e) +
        (Triangle.area △ q:h:f + Triangle.area △ q:f:p) := by
  euclid_apply (sum_parallelograms_area o p e f q h OP EF AE DF)
  euclid_finish

end Elements.Book2
