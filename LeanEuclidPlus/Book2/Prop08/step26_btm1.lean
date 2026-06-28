import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- btm1: bottom strip (a-d-m-n) cut by CH (c on a-d, g on m-n) — its 2 halves (diagonal
   a-n) equal AG + the bottom-rest halves. Canonical vertex orders. -/
theorem helper_2_8_step26_btm1 (a b c d e m n g : Point)
    (AB AE CH DF MN ED : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE)
    (h_d_df : d.onLine DF) (h_n_df : n.onLine DF)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH)
    (h_m_mn : m.onLine MN) (h_g_mn : g.onLine MN) (h_n_mn : n.onLine MN)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED)
    (h_ae_eq : |(a─e)| = |(a─d)|)
    (h_mgn : between m g n) (h_btm1par : formParallelogram a d m n AB MN AE DF)
    (h_dae : ∠ d:a:e = ∟) :
    Triangle.area △ a:m:n + Triangle.area △ a:n:d =
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
        (Triangle.area △ c:g:n + Triangle.area △ c:n:d) := by
  have h_acd : between a c d := by euclid_finish
  euclid_apply (sum_parallelograms_area a d m n c g AB MN AE DF)
  euclid_finish

end Elements.Book2
