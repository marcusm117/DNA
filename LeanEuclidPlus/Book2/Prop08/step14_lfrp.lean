import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step14_lfrp (l f r p : Point) (EF OP BL DF : Line)
    (h_l_ef : l.onLine EF) (h_f_ef : f.onLine EF) (h_r_op : r.onLine OP) (h_p_op : p.onLine OP)
    (h_l_bl : l.onLine BL) (h_r_bl : r.onLine BL) (h_f_df : f.onLine DF) (h_p_df : p.onLine DF)
    (h_efop : ¬(EF.intersectsLine OP)) (h_bldf : ¬(BL.intersectsLine DF))
    (h_ef_ne_op : EF ≠ OP) (h_lrdf : l.sameSide r DF) :
    formParallelogram l f r p EF OP BL DF := by
  euclid_finish

end Elements.Book2
