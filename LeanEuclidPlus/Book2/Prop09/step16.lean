import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop09.step13_befb
import Book2.Prop09.step13_egc
import Book2.Prop09.step16_fdb
import Book2.Prop09.step16_fbd
import Book2.Prop09.step16_formtri
import Book2.Prop09.step16_sum
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step16 (2.9.16): ∠FDB = ∟ and ∠BFD = ∟/2. Geometry (no ∟/2) in step16_fdb (right
-- angle), step16_fbd (∠f:b:d = ∠e:b:c), step16_formtri, step16_sum; linarith combines
-- with step11's ∠e:b:c = ∟/2 → ∠b:f:d = ∟/2.
theorem helper_2_9_step16
  (a b c d e f g e0 e1 : Point) (AB CE EB DF FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hpar_df : ¬DF.intersectsLine CE)
  (hpar_fg : ¬FG.intersectsLine AB)
  (hstep1 : ∠ a:c:e = ∟)
  (h11 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2) :
  ∠ f:d:b = ∟ ∧ ∠ b:f:d = ∟ / 2 := by
  have step13_befb : between e f b := by euclid_apply (helper_2_9_step13_befb b c d e e0 e1 f AB CE DF EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step13_egc : between e g c := by euclid_apply (helper_2_9_step13_egc a b c e f g e0 e1 AB CE EB FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step16_fdb : ∠ f:d:b = ∟ := by euclid_apply (helper_2_9_step16_fdb a b c d e f g e0 e1 AB CE DF EB FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step16_fbd : ∠ f:b:d = ∠ e:b:c := by euclid_apply (helper_2_9_step16_fbd a b c d e f e0 e1 AB CE EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step16_formtri : formTriangle b f d EB DF AB := by euclid_apply (helper_2_9_step16_formtri a b c d e f e0 e1 AB CE DF EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step16_sum : ∠ f:b:d + ∠ b:f:d = ∟ := by euclid_apply (helper_2_9_step16_sum a b c d e f AB CE DF EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  refine ⟨step16_fdb, ?_⟩
  linarith

end Elements.Book2
