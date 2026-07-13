import SystemE
import Book3.Prop03.Main
import Book1.Prop47.Main
import Helpers.OffLine
import Mathlib.Tactic.Linarith
import Book3.Prop35.step5_47fa
import Book3.Prop35.step5_47fc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1 Elements

theorem helper_3_35_step5 (a c e f g : Point) (ABCD : Circle) (AC : Line)
  (ha : a.onCircle ABCD) (hc : c.onCircle ABCD) (hfc : f.isCentre ABCD)
  (hbet_aec : between a e c)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hgAC : g.onLine AC)
  (hgperp : ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟)
  (hassump1 : (∠ a:g:f = ∟ ∨ ∠ c:g:f = ∟) ∧ ¬f.onLine AC)   -- @assumption
  : |(a─g)| = |(g─c)| := by
  have hf_ac : ¬f.onLine AC := hassump1.2
  euclid_apply (line_from_points f g) as FG
  -- The foot g of the perpendicular from the centre is the midpoint (equal radii + Pythagoras),
  -- hence lies between the endpoints — the hypothesis III.3 needs.
  have step5_47fa : |(f─a)| * |(f─a)| = |(g─a)| * |(g─a)| + |(g─f)| * |(g─f)| := by euclid_apply (helper_3_35_step5_47fa a f g AC FG (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine AC; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)))
  have step5_47fc : |(f─c)| * |(f─c)| = |(g─c)| * |(g─c)| + |(g─f)| * |(g─f)| := by euclid_apply (helper_3_35_step5_47fc c f g AC FG (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine AC; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AC → p ≠ g → ∠ p:g:f = ∟; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show ¬f.onLine AC; assumption)))
  have hrad : |(f─a)| = |(f─c)| := by euclid_finish
  have hfsq : |(f─a)| * |(f─a)| = |(f─c)| * |(f─c)| := by rw [hrad]
  have hsq : |(g─a)| * |(g─a)| = |(g─c)| * |(g─c)| := by linarith [step5_47fa, step5_47fc, hfsq]
  have hbisect : |(g─a)| = |(g─c)| := by
    rcases mul_self_eq_mul_self_iff.mp hsq with h | h
    · exact h
    · have h1 := segment_gte_zero (g─a)
      have h2 := segment_gte_zero (g─c)
      linarith
  have hbet : between a g c := by euclid_finish
  euclid_apply (proposition_3 a c f g ABCD AC FG)
  euclid_finish

end Elements.Book3
