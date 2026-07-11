import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step4
    (m n l e : Point) (ABCD : Circle)
    (hm_on : m.onCircle ABCD)
    (hn_on : n.onCircle ABCD)
    (hbetw : between m l n)
    (hperp : ∠ m:l:e = ∟) :
    m.onCircle ABCD ∧ n.onCircle ABCD ∧ between m l n ∧ ∠ m:l:e = ∟ :=
  ⟨hm_on, hn_on, hbetw, hperp⟩

end Elements.Book3
