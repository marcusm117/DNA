import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- btm2: bottom-rest rectangle (c-d-g-n) cut by BL (b on c-d, k on g-n). -/
theorem helper_2_8_step26_btm2 (a b c d g k n : Point)
    (AB CH DF MN BL : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL)
    (h_d_df : d.onLine DF) (h_n_df : n.onLine DF)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_n_mn : n.onLine MN)
    (h_gkn : between g k n) (h_btm2par : formParallelogram c d g n AB MN CH DF) :
    Triangle.area △ c:g:n + Triangle.area △ c:n:d =
      (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
        (Triangle.area △ k:b:d + Triangle.area △ k:d:n) := by
  have h_cbd : between c b d := by euclid_finish
  euclid_apply (sum_parallelograms_area c d g n b k AB MN CH DF)
  euclid_finish

end Elements.Book2
