import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop22.step9_split_a
import Book3.Prop22.step9_split_c
import Book3.Prop22.step9_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step9 (a b c d : Point) (AC BD : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
  (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hbd : b ≠ d)
  (hbAC : ¬b.onLine AC) (hdAC : ¬d.onLine AC) (hbd_opp : ¬b.sameSide d AC)
  (haBD : ¬a.onLine BD) (hcBD : ¬c.onLine BD) (hac_opp : ¬a.sameSide c BD)
  (hstep2 : ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟)
  (hstep8 : ∠ a:b:c + ∠ c:d:a = ∟ + ∟)
  : ∠ d:a:b + ∠ b:c:d = ∟ + ∟ := by
  have step9_split_a : ∠ d:a:b = ∠ d:a:c + ∠ c:a:b := by euclid_apply (helper_3_22_step9_split_a a b c d AC BD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.sameSide d AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide c BD; assumption)))
  have step9_split_c : ∠ b:c:d = ∠ b:c:a + ∠ a:c:d := by euclid_apply (helper_3_22_step9_split_c a b c d AC BD (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬d.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.sameSide d AC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬c.onLine BD; assumption)) (by euclid_assumption "" (show ¬a.sameSide c BD; assumption)))
  have step9_tri : ∠ d:a:c + ∠ a:c:d + ∠ c:d:a = ∟ + ∟ := by euclid_apply (helper_3_22_step9_tri a c d AC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬d.onLine AC; assumption)))
  linarith [step9_split_a, step9_split_c, step9_tri, hstep2, hstep8]

end Elements.Book3
