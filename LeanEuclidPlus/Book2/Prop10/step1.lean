import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
-- step1 (2.10.1): CE ⟂ AD at C, so ∠ACE = ∟. e0 is the prop-11 foot with ∠a:c:e0 = ∟;
-- e lies on ray c→e1 (between c e e1), as does e0 (between c e0 e1), so ∠a:c:e = ∠a:c:e0 via equal_angles.
theorem helper_2_10_step1
  (a b c e e0 e1 : Point) (AC' CE : Line)
  (hacb : between a c b)
  (hac_a : a.onLine AC') (hac_c : c.onLine AC')
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hbte0 : between c e0 e1) (hbte : between c e e1)
  (hperp : ∠ a:c:e0 = ∟) : ∠ a:c:e = ∟ := by
  euclid_apply (equal_angles c a a e e0 AC' CE)
  euclid_finish

end Elements.Book2
