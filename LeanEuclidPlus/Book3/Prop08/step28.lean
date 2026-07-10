import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_8_step28
    (ABC : Circle) (d k n : Point)
    (hn_circ : n.onCircle ABC)
    (hn_dist : |(d─n)| = |(d─k)|) :
    n.onCircle ABC ∧ |(d─n)| = |(d─k)| :=
  ⟨hn_circ, hn_dist⟩

end Elements.Book3
