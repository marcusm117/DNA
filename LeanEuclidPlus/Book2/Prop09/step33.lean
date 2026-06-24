import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_9_step33
  (a b c d e f e0 e1 : Point) (AB CE EA EB DF : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (hea_e : e.onLine EA) (hea_a : a.onLine EA)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hpar_df : ¬DF.intersectsLine CE)
  (hstep12 : ∠ a:e:b = ∟) :
  ∠ a:e:f = ∟ := by
  -- @args: b c d e e0 e1 f AB CE DF EB
  have step13_befb : between e f b := by sorry
  euclid_apply (equal_angles e a a f b EA EB)
  euclid_finish

end Elements.Book2
