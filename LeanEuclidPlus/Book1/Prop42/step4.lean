import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_42_step4 (a : Point) (AG BC : Line)
    (h_a_AG : a.onLine AG) (h_par : ¬AG.intersectsLine BC) :
    a.onLine AG ∧ ¬AG.intersectsLine BC :=
  ⟨h_a_AG, h_par⟩

end Elements.Book1
