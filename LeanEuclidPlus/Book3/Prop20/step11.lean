import SystemE
import Book3.Prop20.step6_isoc
import Book3.Prop20.step6_ext
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step11
  (b d e g : Point) (DEG : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_d_circ : d.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_g_circ : g.onCircle ABC)
  (h_d_DEG : d.onLine DEG) (h_e_DEG : e.onLine DEG) (h_g_DEG : g.onLine DEG)
  (h_bne_d : b ≠ d) (h_bet : between g e d)
  : ∠ g:e:b = ∠ e:d:b + ∠ e:d:b := by
  -- @args: d b e DEG ABC
  have step6_isoc : ∠ e:d:b = ∠ e:b:d := by euclid_apply (helper_3_20_step6_isoc d b e DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)))
  -- @args: d b e g DEG ABC
  have step6_ext : ∠ g:e:b = ∠ e:d:b + ∠ e:b:d := by euclid_apply (helper_3_20_step6_ext d b e g DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show between g e d; assumption)))
  euclid_finish

end Elements.Book3
