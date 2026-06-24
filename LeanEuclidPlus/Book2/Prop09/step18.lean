import SystemE
import Book.Prop06
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

set_option systemE.solverTime 30 in
theorem helper_2_9_step18
  (a b c d e f e0 e1 : Point) (AB CE EB DF FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG)
  (hpar_df : ¬DF.intersectsLine CE)
  (hpar_fg : ¬FG.intersectsLine AB)
  (hstep17 : ∠ f:b:d = ∠ d:f:b) :
  |(f─d)| = |(d─b)| := by
  -- @args: b c d e e0 e1 f AB CE DF EB
  have step13_befb : between e f b := by sorry
  have step18_formtri : formTriangle d b f AB EB DF := by sorry
  euclid_apply (proposition_6 d b f AB EB DF)
  euclid_finish

end Elements.Book2
