import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
-- step16 helper: ∠f:b:d = ∠e:b:c (f on ray b→e via between e f b; d on ray b→c via
-- between c d b). equal_angles at vertex b.
theorem helper_2_9_step16_fbd
  (a b c d e f e0 e1 : Point) (AB CE EB : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (hbefb : between e f b) :
  ∠ f:b:d = ∠ e:b:c := by
  euclid_apply (equal_angles b f e d c EB AB)
  euclid_finish

end Elements.Book2
