import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sq2: upper region (m-e-n-f) cut by OP (o on m-e, p on n-f) — its 2 halves (diagonal
   m-f) equal the mid-strip halves + top-strip halves. Canonical vertex orders. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_sq2 (a b c d e f m n o p : Point)
    (AB AE DF EF MN OP : Line)
    (h_a_ab : a.onLine AB) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF) (h_n_df : n.onLine DF) (h_p_df : p.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_m_mn : m.onLine MN) (h_n_mn : n.onLine MN)
    (h_o_op : o.onLine OP) (h_p_op : p.onLine OP)
    (h_moe : between m o e) (h_npf : between n p f)
    (h_sq2par : formParallelogram m e n f AE DF MN EF) :
    Triangle.area △ m:n:f + Triangle.area △ m:f:e =
      (Triangle.area △ m:n:p + Triangle.area △ m:p:o) +
        (Triangle.area △ o:p:f + Triangle.area △ o:f:e) := by
  euclid_apply (sum_parallelograms_area m e n f o p AE DF MN EF)
  euclid_finish

end Elements.Book2
