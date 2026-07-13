import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop32.step11_split
import Book3.Prop32.step11_transfer
import Book3.Prop32.step11_split_e
import Book3.Prop32.step11_transfer_c
import Book3.Prop32.step11_i13
import Book3.Prop32.step11_iii22
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- "in the alternate segment": the tangent–chord result, proved by Euclid for the perpendicular
-- endpoint `a'`, is carried to the GENERIC segment point `a` via [Prop.~3.21] (angles in the same
-- segment). Euclid's single figure is the ACUTE case (∠FBD ≤ ∟, so `a'` lies in segment BAD with `a`);
-- the OBTUSE case (`a'` in DCB) is his implicit generic-position gloss — there the antipode gives the
-- E-side angle and the F-side follows by the I.13 / III.22 duality.
theorem helper_3_32_step11 (a a' b c d e f : Point) (ABCD : Circle) (BD BA EF : Line)
    (h_a_circ : a.onCircle ABCD) (h_b_circ : b.onCircle ABCD) (h_c_circ : c.onCircle ABCD)
    (h_d_circ : d.onCircle ABCD) (h_a'_circ : a'.onCircle ABCD)
    (h_a_offBD : ¬a.onLine BD) (h_c_offBD : ¬c.onLine BD) (h_e_offBD : ¬e.onLine BD) (h_f_offBD : ¬f.onLine BD)
    (h_af_opp : ¬a.sameSide f BD) (h_ce_opp : ¬c.sameSide e BD)
    (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD) (h_bd : b ≠ d) (h_ba' : b ≠ a') (h_da' : d ≠ a')
    (h_a'_BA : a'.onLine BA) (h_b_BA : b.onLine BA)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_b_EF : b.onLine EF) (h_ebf : between e b f)
    (h_a'_perp : ∠ a':b:f = ∟) (h_notint : ¬EF.intersectsCircle ABCD)
    (step9 : ∠ a':b:f = ∠ b:a':d + ∠ a':b:d) :
    ∠ f:b:d = ∠ b:a:d := by
  -- a' is off BD (a diameter endpoint distinct from b and d)
  have h_a'_offBD : ¬a'.onLine BD := by euclid_finish
  by_cases hac : a'.opposingSides f BD
  · -- ACUTE: the antipode a' lies in segment BAD (same side of BD as a)
    obtain ⟨-, -, h_a'f_opp⟩ := hac
    have step11_split : ∠ f:b:d = ∠ b:a':d := by euclid_apply (helper_3_32_step11_split a' b d e f ABCD BD BA EF (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show ¬a'.onLine BD; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)) (by euclid_assumption "" (show ¬a'.sameSide f BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show ∠ a':b:f = ∟; assumption)) (by euclid_assumption "" (show ¬EF.intersectsCircle ABCD; assumption)) (by euclid_assumption "" (show ∠ a':b:f = ∠ b:a':d + ∠ a':b:d; assumption)))
    have step11_transfer : ∠ b:a:d = ∠ b:a':d := by euclid_apply (helper_3_32_step11_transfer a a' b d f ABCD BD (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬a'.onLine BD; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide f BD; assumption)) (by euclid_assumption "" (show ¬a'.sameSide f BD; assumption)))
    euclid_finish
  · -- OBTUSE: the antipode a' lies in segment DCB (a' opposite e); use the E-side angle + duality
    have h_a'_oppe : a'.opposingSides e BD := by euclid_finish
    obtain ⟨-, -, h_a'e_opp⟩ := h_a'_oppe
    have h_sum7 : ∠ b:a':d + ∠ a':b:d = ∟ := by euclid_finish
    have step11_split_e : ∠ e:b:d = ∠ b:a':d := by euclid_apply (helper_3_32_step11_split_e a' b d e f ABCD BD BA EF (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show ¬a'.onLine BD; assumption)) (by euclid_assumption "" (show ¬e.onLine BD; assumption)) (by euclid_assumption "" (show ¬a'.sameSide e BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a'.onLine BA; assumption)) (by euclid_assumption "" (show b.onLine BA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show ∠ a':b:f = ∟; assumption)) (by euclid_assumption "" (show ¬EF.intersectsCircle ABCD; assumption)) (by euclid_assumption "" (show ∠ b:a':d + ∠ a':b:d = ∟; assumption)))
    have step11_transfer_c : ∠ b:c:d = ∠ b:a':d := by euclid_apply (helper_3_32_step11_transfer_c c a' b d e ABCD BD (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show a'.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬a'.onLine BD; assumption)) (by euclid_assumption "" (show ¬e.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.sameSide e BD; assumption)) (by euclid_assumption "" (show ¬a'.sameSide e BD; assumption)))
    have step11_i13 : ∠ f:b:d + ∠ e:b:d = ∟ + ∟ := by euclid_apply (helper_3_32_step11_i13 b d e f BD EF (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)))
    have step11_iii22 : ∠ b:a:d + ∠ b:c:d = ∟ + ∟ := by euclid_apply (helper_3_32_step11_iii22 a b c d e f ABCD BD EF (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬e.onLine BD; assumption)) (by euclid_assumption "" (show ¬f.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide f BD; assumption)) (by euclid_assumption "" (show ¬c.sameSide e BD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)))
    linarith [step11_split_e, step11_transfer_c, step11_i13, step11_iii22]

end Elements.Book3
