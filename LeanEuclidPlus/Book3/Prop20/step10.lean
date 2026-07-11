import SystemE
import Book3.Prop20.step6_isoc
import Book3.Prop20.step6_ext
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step10
  (c d e g : Point) (DEG : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_d_circ : d.onCircle ABC) (h_c_circ : c.onCircle ABC)
  (h_g_circ : g.onCircle ABC)
  (h_d_DEG : d.onLine DEG) (h_e_DEG : e.onLine DEG) (h_g_DEG : g.onLine DEG)
  (h_cne_d : c ≠ d) (h_bet : between g e d)
  : ∠ g:e:c = ∠ e:d:c + ∠ e:d:c := by
  -- @args: d c e DEG ABC
  have step6_isoc : ∠ e:d:c = ∠ e:c:d := by euclid_apply (helper_3_20_step6_isoc d c e DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)))
  -- @args: d c e g DEG ABC
  have step6_ext : ∠ g:e:c = ∠ e:d:c + ∠ e:c:d := by euclid_apply (helper_3_20_step6_ext d c e g DEG ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show d.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DEG; assumption)) (by euclid_assumption "" (show e.onLine DEG; assumption)) (by euclid_assumption "" (show g.onLine DEG; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show between g e d; assumption)))
  euclid_finish

end Elements.Book3
