import SystemE
import Helpers.OffLine
import Book2.Prop09.step13_befb
import Book2.Prop09.step36_pf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_9_step36
  (a b c d e f e0 e1 : Point) (AB CE DF EB : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hpar_df : ¬DF.intersectsLine CE)
  (hstep16 : ∠ f:d:b = ∟ ∧ ∠ b:f:d = ∟ / 2) :
  ∠ a:d:f = ∟ := by
  -- @args: b c d e e0 e1 f AB CE DF EB
  have step13_befb : between e f b := by euclid_apply (helper_2_9_step13_befb b c d e e0 e1 f AB CE DF EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hfdb : ∠ f:d:b = ∟ := hstep16.1
  have step36_pf : ∠ a:d:f = ∟ := by euclid_apply (helper_2_9_step36_pf a b c d e f e0 e1 AB CE DF EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  exact step36_pf

end Elements.Book2
