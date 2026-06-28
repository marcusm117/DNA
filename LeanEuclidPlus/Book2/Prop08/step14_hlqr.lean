import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step14_hlqr (h l q r : Point) (EF OP CH BL : Line)
    (h_h_ef : h.onLine EF) (h_l_ef : l.onLine EF) (h_q_op : q.onLine OP) (h_r_op : r.onLine OP)
    (h_h_ch : h.onLine CH) (h_q_ch : q.onLine CH) (h_l_bl : l.onLine BL) (h_r_bl : r.onLine BL)
    (h_efop : ¬(EF.intersectsLine OP)) (h_chbl : ¬(CH.intersectsLine BL))
    (h_ef_ne_op : EF ≠ OP) (h_hqbl : h.sameSide q BL) :
    formParallelogram h l q r EF OP CH BL := by
  euclid_finish

end Elements.Book2
