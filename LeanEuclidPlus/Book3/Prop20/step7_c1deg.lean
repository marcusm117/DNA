import SystemE
import Book3.Prop20.step7_c1deg_fbc
import Book3.Prop20.step7_c1deg_fb
import Book3.Prop20.step7_c1deg_fc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_c1deg
  (a b c e f : Point) (BC AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_c_circ : c.onCircle ABC) (h_f_circ : f.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_bne_a : b ≠ a) (h_cne_a : c ≠ a) (h_aSe : a.sameSide e BC) (h_bet : between f e a)
  (step5 : ∠ b:e:f = ∠ e:a:b + ∠ e:a:b) (step6 : ∠ f:e:c = ∠ e:a:c + ∠ e:a:c)
  (hfBC : f.onLine BC)
  : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by
  -- f on the chord BC and on the circle ⟹ f = b or f = c (a line meets a circle in ≤2 points).
  have step7_c1deg_fbc : f = b ∨ f = c := by euclid_apply (helper_3_20_step7_c1deg_fbc b c e f BC ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show f.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)))
  rcases step7_c1deg_fbc with h | h
  · have step7_c1deg_fb : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by euclid_apply (helper_3_20_step7_c1deg_fb a b c e f BC AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)) (by euclid_assumption "" (show between f e a; assumption)) (by euclid_assumption "" (show ∠ b:e:f = ∠ e:a:b + ∠ e:a:b; assumption)) (by euclid_assumption "" (show ∠ f:e:c = ∠ e:a:c + ∠ e:a:c; assumption)) (by euclid_assumption "" (show f = b; assumption)))
    exact step7_c1deg_fb
  · have step7_c1deg_fc : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by euclid_apply (helper_3_20_step7_c1deg_fc a b c e f BC AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)) (by euclid_assumption "" (show between f e a; assumption)) (by euclid_assumption "" (show ∠ b:e:f = ∠ e:a:b + ∠ e:a:b; assumption)) (by euclid_assumption "" (show ∠ f:e:c = ∠ e:a:c + ∠ e:a:c; assumption)) (by euclid_assumption "" (show f = c; assumption)))
    exact step7_c1deg_fc

end Elements.Book3
