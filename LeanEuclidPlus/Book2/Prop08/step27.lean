import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop08.step27_sq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- step27: 4|ab||bd| + |ac|² = |ad|².
   Combine step25 (LHS = 9 figures), step26 (9 figures = △aef+△afd) and the
   square-area fact step27_sq (△aef+△afd = |ad|²) by linarith. No euclid_finish
   here, so the product-terms in the hyps/goal are handled as atoms by linarith. -/
theorem helper_2_8_step27 (a b c d e f g k n m o q r l h p : Point)
    (AB AE DF EF : Line)
    (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_c_ab : c.onLine AB)
    (h_acb : between a c b) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE)
    (h_d_df : d.onLine DF) (h_f_df : f.onLine DF)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF)
    (h_ae_eq : |(a─e)| = |(a─d)|) (h_df_eq : |(d─f)| = |(a─d)|)
    (h_ae_df : ¬(AE.intersectsLine DF)) (h_ef_ab : ¬(EF.intersectsLine AB))
    (h_dae : ∠ d:a:e = ∟) (h_aef : ∠ a:e:f = ∟)
    (h_step25 : 4 * (|(a─b)| * |(b─d)|) + |(a─c)| * |(a─c)| =
      (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) +
      (Triangle.area △ o:q:h + Triangle.area △ o:h:e))
    (h_step26 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) +
      (Triangle.area △ o:q:h + Triangle.area △ o:h:e) =
      Triangle.area △ a:e:f + Triangle.area △ a:f:d) :
    4 * (|(a─b)| * |(b─d)|) + |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)| := by
  have step27_sq : Triangle.area △ a:e:f + Triangle.area △ a:f:d = |(a─d)| * |(a─d)| := by euclid_apply (helper_2_8_step27_sq a b c d e f AB AE DF EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:e:f = ∟; assumption)))
  linarith

end Elements.Book2
