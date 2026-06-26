import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop09.step13_befb
import Book2.Prop09.step13_egc
import Book2.Prop09.step13_fsb
import Book2.Prop09.step13_rcb
import Book2.Prop09.step13_egf
import Book2.Prop09.step13_geo
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

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
  have step13_befb : between e f b := by euclid_apply (helper_2_9_step13_befb b c d e e0 e1 f AB CE DF EB (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AB; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ¬DF.intersectsLine CE; assumption)))
  have step13_egc : between e g c := by euclid_apply (helper_2_9_step13_egc a b c e f g e0 e1 AB CE EB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show g.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine AB; assumption)) (by euclid_assumption "" (show between e f b; assumption)))
  have step13_fsb : f.sameSide b CE := by euclid_apply (helper_2_9_step13_fsb a b c d e f e0 e1 AB CE DF EB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AB; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ¬DF.intersectsLine CE; assumption)) (by euclid_assumption "" (show between e f b; assumption)))
  have step13_rcb : ∠ g:c:b = ∟ := by euclid_apply (helper_2_9_step13_rcb a b c e g e1 AB CE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show g.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show between e g c; assumption)) (by euclid_assumption "" (show ∠ a:c:e = ∟; assumption)))
  have step13_egf : ∠ e:g:f = ∟ := by euclid_apply (helper_2_9_step13_egf a b c d e f g e0 e1 AB CE EB DF FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show g.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AB; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine AB; assumption)) (by euclid_assumption "" (show f.sameSide b CE; assumption)) (by euclid_assumption "" (show between e g c; assumption)) (by euclid_assumption "" (show ∠ g:c:b = ∟; assumption)))
  have step13_geo : (∠ g:e:f = ∠ c:e:b) ∧ (∠ g:e:f + ∠ e:f:g = ∟) := by euclid_apply (helper_2_9_step13_geo a b c d e f g e0 e1 AB CE DF EB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show g.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AB; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show ¬DF.intersectsLine CE; assumption)) (by euclid_assumption "" (show between e g c; assumption)) (by euclid_assumption "" (show between e f b; assumption)) (by euclid_assumption "" (show ∠ e:g:f = ∟; assumption)))
  refine ⟨step13_egf, ?_⟩
  linarith

end Elements.Book2
