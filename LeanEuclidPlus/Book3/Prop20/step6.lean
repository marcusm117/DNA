import SystemE
import Book3.Prop20.step6_isoc
import Book3.Prop20.step6_ext
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step6
  (a c e f : Point) (AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_c_circ : c.onCircle ABC)
  (h_f_circ : f.onCircle ABC)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_cne_a : c ≠ a) (h_bet : between f e a)
  : ∠ f:e:c = ∠ e:a:c + ∠ e:a:c := by
  have step6_isoc : ∠ e:a:c = ∠ e:c:a := by euclid_apply (helper_3_20_step6_isoc a c e AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)))
  have step6_ext : ∠ f:e:c = ∠ e:a:c + ∠ e:c:a := by euclid_apply (helper_3_20_step6_ext a c e f AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show between f e a; assumption)))
  euclid_finish

end Elements.Book3
