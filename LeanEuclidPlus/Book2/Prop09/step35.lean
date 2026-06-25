import SystemE
import Book.Prop47
import Helpers.OffLine
import Mathlib.Tactic.Linarith
import Book2.Prop09.step13_befb
import Book2.Prop09.step35_formtri
import Book2.Prop09.step35_adf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

theorem helper_2_9_step35
  (a b c d e f e0 e1 : Point) (AB CE DF EB AF FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG)
  (haf_a : a.onLine AF) (haf_f : f.onLine AF)
  (hpar_df : ¬DF.intersectsLine CE)
  (hpar_fg : ¬FG.intersectsLine AB)
  (hstep16 : ∠ f:d:b = ∟ ∧ ∠ b:f:d = ∟ / 2) :
  |(a─d)| * |(a─d)| + |(d─f)| * |(d─f)| = |(a─f)| * |(a─f)| := by
  -- @args: b c d e e0 e1 f AB CE DF EB
  have step13_befb : between e f b := by euclid_apply (helper_2_9_step13_befb b c d e e0 e1 f AB CE DF EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hfdb : ∠ f:d:b = ∟ := hstep16.1
  have step35_formtri : formTriangle d a f AB AF DF := by euclid_apply (helper_2_9_step35_formtri a b c d e f e0 e1 AB CE DF EB AF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step35_adf : ∠ a:d:f = ∟ := by euclid_apply (helper_2_9_step35_adf a b c d e f e0 e1 AB CE DF EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_apply (proposition_47 d a f AB AF DF)
  euclid_finish

end Elements.Book2
