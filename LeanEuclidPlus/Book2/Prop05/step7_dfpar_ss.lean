import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- d.sameSide b EF: d,b both on AB; both off EF (from doff/boff sub-nodes); EF∥AB.
   By contradiction: if d opposes b across EF, then EF crosses AB — contradicts hEFAB. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_dfpar_ss (b d : Point) (AB EF : Line)
    (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hdoffEF : ¬(d.onLine EF))
    (hboffEF : ¬(b.onLine EF))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    d.sameSide b EF := by
  euclid_intros
  have hEFneAB : EF ≠ AB := fun heq => hdoffEF (heq ▸ hdAB)
  by_contra hns
  euclid_apply (intersection_lines_opposing d b EF AB)
  euclid_finish

end Elements.Book2
