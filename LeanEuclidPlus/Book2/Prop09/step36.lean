import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
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
  have step13_befb : between e f b := by sorry
  have hfdb : ∠ f:d:b = ∟ := hstep16.1
  have step36_pf : ∠ a:d:f = ∟ := by sorry
  exact step36_pf

end Elements.Book2
