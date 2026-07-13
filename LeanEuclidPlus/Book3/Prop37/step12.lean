import SystemE
import Book1.Prop08.Main
import Book3.Prop37.step12_foffDE
import Book3.Prop37.step12_pyth
import Book3.Prop37.step12_fdb
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_37_step12 (d e f b : Point) (ABC : Circle) (DE FD FE FB DB : Line)
    (h_e_DE : e.onLine DE) (h_d_DE : d.onLine DE)
    (h_f_FE : f.onLine FE) (h_e_FE : e.onLine FE)
    (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD)
    (h_f_FB : f.onLine FB) (h_b_FB : b.onLine FB)
    (h_b_DB : b.onLine DB) (h_d_DB : d.onLine DB)
    (h_fe : f ≠ e) (h_fb : f ≠ b) (h_fd : f ≠ d)
    (h_e_circ : e.onCircle ABC) (h_b_circ : b.onCircle ABC) (h_d_noc : ¬ d.onCircle ABC)
    (h_cen : f.isCentre ABC) (h_nint : ¬ DE.intersectsCircle ABC)
    (h_angle : ∠ f:e:d = ∟)
    (h_step10 : |(d─e)| = |(d─b)| ∧ |(e─f)| = |(b─f)|) :
    ∠ d:e:f = ∠ d:b:f := by
  obtain ⟨h_de_db, h_ef_bf⟩ := h_step10
  have h_fe_fb : |(f─e)| = |(f─b)| := by
    rw [segment_symmetric f e, segment_symmetric f b]; exact h_ef_bf
  have h_bd : b ≠ d := by euclid_finish
  have step12_foffDE : ¬ f.onLine DE := by euclid_apply (helper_3_37_step12_foffDE f ABC DE (by euclid_assumption "" (show ¬ DE.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)))
  have step12_pyth : |(f─d)| * |(f─d)| = |(f─e)| * |(f─e)| + |(e─d)| * |(e─d)| := by euclid_apply (helper_3_37_step12_pyth d e f ABC DE FE FD (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f ≠ e; assumption)) (by euclid_assumption "" (show f ≠ d; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬ d.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬ f.onLine DE; assumption)) (by euclid_assumption "" (show ∠ f:e:d = ∟; assumption)))
  have step12_fdb : ¬ f.onLine DB := by euclid_apply (helper_3_37_step12_fdb d e f b DB (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show |(f─d)| * |(f─d)| = |(f─e)| * |(f─e)| + |(e─d)| * |(e─d)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(d─b)|; assumption)) (by euclid_assumption "" (show |(f─e)| = |(f─b)|; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show f ≠ d; assumption)))
  euclid_apply (proposition_8 e d f b d f DE FD FE DB FD FB)
  euclid_finish

end Elements.Book3
