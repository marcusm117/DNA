import SystemE
import Book1.Prop42.step6_ebc
import Book1.Prop42.step6_dptcg
import Book1.Prop42.step6_same
import Book1.Prop42.step6_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step6 (a b e f g c : Point) (AB BC AG EF CG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_AB_ne_BC : AB ≠ BC)
    (h_a_AG : a.onLine AG)
    (h_f_AG : f.onLine AG) (h_f_EF : f.onLine EF)
    (h_g_CG : g.onLine CG) (h_g_AG : g.onLine AG)
    (h_e_EF : e.onLine EF)
    (h_c_CG : c.onLine CG)
    (h_bet : between b e c)
    (h_par_AG_BC : ¬AG.intersectsLine BC)
    (h_par_CG_EF : ¬CG.intersectsLine EF) :
    formParallelogram f g e c AG BC EF CG := by
  have step6_ebc : e.onLine BC := by euclid_apply (helper_1_42_step6_ebc b e c BC (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show between b e c; assumption)))
  have step6_dptcg : distinctPointsOnLine g c CG := by euclid_apply (helper_1_42_step6_dptcg a b g c AB BC AG CG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine CG; assumption)) (by euclid_assumption "" (show c.onLine CG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show ¬AG.intersectsLine BC; assumption)))
  have step6_same : f.sameSide e CG := by euclid_apply (helper_1_42_step6_same a b e f g c AB BC AG EF CG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show g.onLine CG; assumption)) (by euclid_assumption "" (show c.onLine CG; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show between b e c; assumption)) (by euclid_assumption "" (show ¬AG.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬CG.intersectsLine EF; assumption)))
  have step6_par : ¬EF.intersectsLine CG := by euclid_apply (helper_1_42_step6_par EF CG (by euclid_assumption "" (show ¬CG.intersectsLine EF; assumption)))
  exact ⟨h_f_AG, h_g_AG, step6_ebc, h_c_BC, h_f_EF, h_e_EF, step6_dptcg, step6_same, h_par_AG_BC, step6_par⟩

end Elements.Book1
