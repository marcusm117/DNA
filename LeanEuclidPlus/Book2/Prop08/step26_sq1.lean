import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sq1: square AEFD cut by MN (m on AE, n on DF) — the 2 halves (diagonal a-f, = goal RHS)
   equal the bottom-strip halves + upper-region halves. Canonical vertex orders. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26_sq1 (a b c d e f m n : Point)
    (AB AE DF EF MN : Line)
    (h_a_ab : a.onLine AB) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF) (h_n_df : n.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_m_mn : m.onLine MN) (h_n_mn : n.onLine MN)
    (h_ame : between a m e) (h_dnf : between d n f)
    (h_sqpar : formParallelogram a e d f AE DF AB EF) :
    Triangle.area △ a:e:f + Triangle.area △ a:f:d =
      (Triangle.area △ a:m:n + Triangle.area △ a:n:d) +
        (Triangle.area △ m:n:f + Triangle.area △ m:f:e) := by
  euclid_apply (sum_parallelograms_area a e d f m n AE DF AB EF)
  euclid_finish

end Elements.Book2
