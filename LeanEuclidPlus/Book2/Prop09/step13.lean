import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
-- step13 (2.9.13): ∠EGF = ∟ and ∠EFG = ∟/2. The betweenness/sameSide/right-angle facts
-- are hoisted leaves here; geometry is in step13_egf (right angle) + step13_geo
-- (∠g:e:f = ∠c:e:b and the angle-sum); linarith combines with step11's ∟/2.
theorem helper_2_9_step13
  (a b c d e f g e0 e1 : Point) (AB CE EB DF FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hpar_df : ¬DF.intersectsLine CE)
  (hpar_fg : ¬FG.intersectsLine AB)
  (hstep1 : ∠ a:c:e = ∟)
  (h11 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2) :
  ∠ e:g:f = ∟ ∧ ∠ e:f:g = ∟ / 2 := by
  have step13_befb : between e f b := by sorry
  have step13_egc : between e g c := by sorry
  have step13_fsb : f.sameSide b CE := by sorry
  have step13_rcb : ∠ g:c:b = ∟ := by sorry
  have step13_egf : ∠ e:g:f = ∟ := by sorry
  have step13_geo : (∠ g:e:f = ∠ c:e:b) ∧ (∠ g:e:f + ∠ e:f:g = ∟) := by sorry
  refine ⟨step13_egf, ?_⟩
  linarith

end Elements.Book2
