import SystemE
import Helpers.SameSide
import Helpers.OffLine
import Helpers.Area
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- step26: the 8 gnomon figures plus the square OH (9 cells) tile the whole square AEFD:
   (9 cells) = △aef + △afd. Pure area tiling via `sum_parallelograms_area` — no length
   products, so the context stays SMT-safe. Hierarchy: sq1+sq2 split the square into 3
   horizontal strips; each strip's two cuts split it into 3 cells (in exact goal vertex
   orders); a final linarith chains the 8 equalities. -/
set_option systemE.solverTime 30 in
theorem helper_2_8_step26 (a b c d e f g k n m o q r l h p : Point)
    (AB AE DF EF ED CH BL MN OP : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_m_ae : m.onLine AE) (h_o_ae : o.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF) (h_n_df : n.onLine DF) (h_p_df : p.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF) (h_h_ef : h.onLine EF) (h_l_ef : l.onLine EF)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_e_ed : e.onLine ED) (h_d_ed : d.onLine ED) (h_k_ed : k.onLine ED) (h_q_ed : q.onLine ED)
    (h_c_ch : c.onLine CH) (h_g_ch : g.onLine CH) (h_q_ch : q.onLine CH) (h_h_ch : h.onLine CH)
    (h_b_bl : b.onLine BL) (h_k_bl : k.onLine BL) (h_r_bl : r.onLine BL) (h_l_bl : l.onLine BL)
    (h_g_mn : g.onLine MN) (h_k_mn : k.onLine MN) (h_m_mn : m.onLine MN) (h_n_mn : n.onLine MN)
    (h_o_op : o.onLine OP) (h_q_op : q.onLine OP) (h_r_op : r.onLine OP) (h_p_op : p.onLine OP)
    (h_ch_ae : ¬(CH.intersectsLine AE)) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_mn_ab : ¬(MN.intersectsLine AB)) (h_op_ab : ¬(OP.intersectsLine AB))
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_aef : ∠ a:e:f = ∟) (h_adf : ∠ a:d:f = ∟)
    (h_bd_eq : |(b─d)| = |(c─b)|) :
    (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) +
      (Triangle.area △ o:q:h + Triangle.area △ o:h:e) =
      Triangle.area △ a:e:f + Triangle.area △ a:f:d := by
  -- betweenness anchors (interior grid points on the side / grid lines)
  have step12_gkgq_ang_qkd : between q k d := by sorry
  have step12_gkgq_ang_kqe : between k q e := by sorry
  have step15_mnef : ¬(MN.intersectsLine EF) := by sorry
  have step13_mnop : ¬(MN.intersectsLine OP) := by sorry
  have step26_chdf : ¬(CH.intersectsLine DF) := by sorry
  have step26_bldf : ¬(BL.intersectsLine DF) := by sorry
  have step7_gkqr_chbl : ¬(CH.intersectsLine BL) := by sorry
  have step14_efop : ¬(EF.intersectsLine OP) := by sorry
  have step21_ame : between a m e := by sorry
  have step26_dnf : between d n f := by sorry
  have step26_npf : between n p f := by sorry
  have step26_moe : between m o e := by sorry
  have step26_mgn : between m g n := by sorry
  have step26_gkn : between g k n := by sorry
  have step26_oqp : between o q p := by sorry
  have step26_qrp : between q r p := by sorry
  have step26_ehf : between e h f := by sorry
  have step26_hlf : between h l f := by sorry
  have step15_qhoe_qoffab : ¬(q.onLine AB) := by sorry
  -- the 8 sum_parallelograms_area cuts (canonical, exact goal vertex orders)
  have step26_aefd : formParallelogram a e d f AE DF AB EF := by sorry
  have step26_sq2_par : formParallelogram m e n f AE DF MN EF := by sorry
  have step26_btm1_par : formParallelogram a d m n AB MN AE DF := by sorry
  have step26_btm2_par : formParallelogram c d g n AB MN CH DF := by sorry
  have step26_mid1_par : formParallelogram m n o p MN OP AE DF := by sorry
  have step26_mid2_par : formParallelogram g n q p MN OP CH DF := by sorry
  have step26_top1_par : formParallelogram o p e f OP EF AE DF := by sorry
  have step26_top2_par : formParallelogram q p h f OP EF CH DF := by sorry
  have step6_cbgk : formParallelogram c b g k AB MN CH BL := by sorry
  have step6_bdkn : formParallelogram b d k n AB MN BL DF := by sorry
  have step26_sq1 : Triangle.area △ a:e:f + Triangle.area △ a:f:d =
      (Triangle.area △ a:m:n + Triangle.area △ a:n:d) +
        (Triangle.area △ m:n:f + Triangle.area △ m:f:e) := by sorry
  have step26_sq2 : Triangle.area △ m:n:f + Triangle.area △ m:f:e =
      (Triangle.area △ m:n:p + Triangle.area △ m:p:o) +
        (Triangle.area △ o:p:f + Triangle.area △ o:f:e) := by sorry
  have step26_btm1 : Triangle.area △ a:m:n + Triangle.area △ a:n:d =
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
        (Triangle.area △ c:g:n + Triangle.area △ c:n:d) := by sorry
  have step26_btm2 : Triangle.area △ c:g:n + Triangle.area △ c:n:d =
      (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
        (Triangle.area △ k:b:d + Triangle.area △ k:d:n) := by sorry
  have step26_mid1 : Triangle.area △ m:n:p + Triangle.area △ m:p:o =
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
        (Triangle.area △ g:q:p + Triangle.area △ g:p:n) := by sorry
  have step26_mid2 : Triangle.area △ g:q:p + Triangle.area △ g:p:n =
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
        (Triangle.area △ k:n:p + Triangle.area △ k:p:r) := by sorry
  have step26_top1 : Triangle.area △ o:p:f + Triangle.area △ o:f:e =
      (Triangle.area △ o:q:h + Triangle.area △ o:h:e) +
        (Triangle.area △ q:h:f + Triangle.area △ q:f:p) := by sorry
  have step26_top2 : Triangle.area △ q:h:f + Triangle.area △ q:f:p =
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
        (Triangle.area △ r:p:f + Triangle.area △ r:f:l) := by sorry
  linarith

end Elements.Book2
