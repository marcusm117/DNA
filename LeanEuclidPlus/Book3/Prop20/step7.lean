import SystemE
import Book3.Prop20.step7_case2
import Book3.Prop20.step7_c1deg
import Book3.Prop20.step7_addA
import Book3.Prop20.step7_addE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7
  (a b c e f : Point) (BC AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_c_circ : c.onCircle ABC) (h_f_circ : f.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_bne_a : b ≠ a) (h_cne_a : c ≠ a) (h_aSe : a.sameSide e BC) (h_bet : between f e a)
  (step5 : ∠ b:e:f = ∠ e:a:b + ∠ e:a:b) (step6 : ∠ f:e:c = ∠ e:a:c + ∠ e:a:c)
  : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by
  by_cases hfs : f.sameSide a BC
  · -- Case 2: E OUTSIDE ∠BAC (diameter AF does NOT separate B,C). Subtraction.
    -- TODO (case 2): prove in step7_case2.lean. Recipe (see agent_notes): crossing x = AEF∩BC
    -- ⟹ b,c same side of AEF; same_side_pigeon_hole picks which of B/C is inside sector FEC;
    -- then the trivial sum_angles leaves (step7_subE / step7_subA) give the subtraction.
    have step7_case2 : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by euclid_apply (helper_3_20_step7_case2 a b c e f BC AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)) (by euclid_assumption "" (show between f e a; assumption)) (by euclid_assumption "" (show ∠ b:e:f = ∠ e:a:b + ∠ e:a:b; assumption)) (by euclid_assumption "" (show ∠ f:e:c = ∠ e:a:c + ∠ e:a:c; assumption)) (by euclid_assumption "" (show f.sameSide a BC; assumption)))
    exact step7_case2
  · -- Case 1: E INSIDE ∠BAC (diameter AF separates B,C). Addition.
    by_cases hfBC : f.onLine BC
    · -- @euclid_gap: f on BC ⟹ f = b or f = c ⟹ AB or AC is a diameter (degenerate);
      -- then ∠EAB or ∠EAC = 0 and the doubling collapses.
      have step7_c1deg : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by euclid_apply (helper_3_20_step7_c1deg a b c e f BC AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)) (by euclid_assumption "" (show between f e a; assumption)) (by euclid_assumption "" (show ∠ b:e:f = ∠ e:a:b + ∠ e:a:b; assumption)) (by euclid_assumption "" (show ∠ f:e:c = ∠ e:a:c + ∠ e:a:c; assumption)) (by euclid_assumption "" (show f.onLine BC; assumption)))
      exact step7_c1deg
    · have hopp : a.opposingSides f BC := by euclid_finish
      have step7_addA : ∠ b:a:c = ∠ b:a:e + ∠ e:a:c := by euclid_apply (helper_3_20_step7_addA a b c e f BC AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)) (by euclid_assumption "" (show between f e a; assumption)) (by euclid_assumption "" (show a.opposingSides f BC; assumption)))
      have step7_addE : ∠ b:e:c = ∠ b:e:f + ∠ f:e:c := by euclid_apply (helper_3_20_step7_addE a b c e f BC AEF ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)) (by euclid_assumption "" (show between f e a; assumption)) (by euclid_assumption "" (show a.opposingSides f BC; assumption)))
      euclid_finish

end Elements.Book3
