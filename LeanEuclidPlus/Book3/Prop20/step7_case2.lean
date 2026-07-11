import SystemE
import Book3.Prop20.step7_case2_hsec
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_case2
  (a b c e f : Point) (BC AEF : Line) (ABC : Circle)
  (h_e_centre : e.isCentre ABC) (h_a_circ : a.onCircle ABC) (h_b_circ : b.onCircle ABC)
  (h_c_circ : c.onCircle ABC) (h_f_circ : f.onCircle ABC)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_bne_c : b ≠ c)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_bne_a : b ≠ a) (h_cne_a : c ≠ a) (h_aSe : a.sameSide e BC) (h_bet : between f e a)
  (step5 : ∠ b:e:f = ∠ e:a:b + ∠ e:a:b) (step6 : ∠ f:e:c = ∠ e:a:c + ∠ e:a:c)
  (hfs : f.sameSide a BC)
  : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c := by
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points a c) as AC
  euclid_apply (line_from_points e b) as EB
  euclid_apply (line_from_points e c) as EC
  have step7_case2_hsec : (f.sameSide b EC ∧ e.sameSide b AC ∧ c.sameSide b AEF) ∨
              (f.sameSide c EB ∧ e.sameSide c AB ∧ b.sameSide c AEF) := by euclid_apply (helper_3_20_step7_case2_hsec a b c e f BC AEF AB AC EB EC ABC (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a.onLine AEF; assumption)) (by euclid_assumption "" (show e.onLine AEF; assumption)) (by euclid_assumption "" (show f.onLine AEF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show a.sameSide e BC; assumption)) (by euclid_assumption "" (show between f e a; assumption)) (by euclid_assumption "" (show f.sameSide a BC; assumption)))
  rcases step7_case2_hsec with ⟨hfbEC, hebAC, hcbAEF⟩ | ⟨hfcEB, hecAB, hbcAEF⟩
  · -- 2a: B inside sectors. ∠fec = ∠feb + ∠bec ; ∠eac = ∠eab + ∠bac.
    euclid_apply (sum_angles_onlyif e f c b AEF EC)
    euclid_apply (sum_angles_onlyif a e c b AEF AC)
    euclid_finish
  · -- 2b: C inside sectors. ∠feb = ∠fec + ∠ceb ; ∠eab = ∠eac + ∠cab.
    euclid_apply (sum_angles_onlyif e f b c AEF EB)
    euclid_apply (sum_angles_onlyif a e b c AEF AB)
    euclid_finish

end Elements.Book3
