import SystemE
import Book3.Prop20.step7_case2
import Book3.Prop20.step7_c1deg
import Book3.Prop20.step7_addA
import Book3.Prop20.step7_addE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Second inscribed vertex D (antipode G): the SAME argument as step7, re-instantiated a→d, f→g.
theorem helper_3_20_step12
  (b c d e g : Point) (BC DEG : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_d_circ : d.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_c_circ : c.onCircle ABC) (h_g_circ : g.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_d_DEG : d.onLine DEG) (h_e_DEG : e.onLine DEG) (h_g_DEG : g.onLine DEG)
  (h_bne_d : b ≠ d) (h_cne_d : c ≠ d) (h_dSe : d.sameSide e BC) (h_bet : between g e d)
  (step10 : ∠ g:e:c = ∠ e:d:c + ∠ e:d:c) (step11 : ∠ g:e:b = ∠ e:d:b + ∠ e:d:b)
  : ∠ b:e:c = ∠ b:d:c + ∠ b:d:c := by
  have step5 : ∠ b:e:g = ∠ e:d:b + ∠ e:d:b := by euclid_finish
  by_cases hgs : g.sameSide d BC
  ·
    -- @args: d b c e g BC DEG ABC
    have step7_case2 : ∠ b:e:c = ∠ b:d:c + ∠ b:d:c := by euclid_apply (helper_3_20_step7_case2 d b c e g BC DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show d.sameSide e BC; assumption)) (by euclid_assumption "" (show between g e d; assumption)) (by euclid_assumption "" (show ∠ b:e:g = ∠ e:d:b + ∠ e:d:b; assumption)) (by euclid_assumption "" (show ∠ g:e:c = ∠ e:d:c + ∠ e:d:c; assumption)) (by euclid_assumption "" (show g.sameSide d BC; assumption)))
    exact step7_case2
  · by_cases hgBC : g.onLine BC
    ·
      -- @args: d b c e g BC DEG ABC
      have step7_c1deg : ∠ b:e:c = ∠ b:d:c + ∠ b:d:c := by euclid_apply (helper_3_20_step7_c1deg d b c e g BC DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show d.sameSide e BC; assumption)) (by euclid_assumption "" (show between g e d; assumption)) (by euclid_assumption "" (show ∠ b:e:g = ∠ e:d:b + ∠ e:d:b; assumption)) (by euclid_assumption "" (show ∠ g:e:c = ∠ e:d:c + ∠ e:d:c; assumption)) (by euclid_assumption "" (show g.onLine BC; assumption)))
      exact step7_c1deg
    · have hopp : d.opposingSides g BC := by euclid_finish
      -- @args: d b c e g BC DEG ABC
      have step7_addA : ∠ b:d:c = ∠ b:d:e + ∠ e:d:c := by euclid_apply (helper_3_20_step7_addA d b c e g BC DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show d.sameSide e BC; assumption)) (by euclid_assumption "" (show between g e d; assumption)) (by euclid_assumption "" (show d.opposingSides g BC; assumption)))
      -- @args: d b c e g BC DEG ABC
      have step7_addE : ∠ b:e:c = ∠ b:e:g + ∠ g:e:c := by euclid_apply (helper_3_20_step7_addE d b c e g BC DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show d.sameSide e BC; assumption)) (by euclid_assumption "" (show between g e d; assumption)) (by euclid_assumption "" (show d.opposingSides g BC; assumption)))
      euclid_finish

end Elements.Book3
