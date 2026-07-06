import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step3 (a b d : Point) (AB DE : Line)
    (hd_on : d.onLine DE) (hpar : ¬(DE.intersectsLine AB)) :
    d.onLine DE ∧ ¬(DE.intersectsLine AB) :=
  ⟨hd_on, hpar⟩

end Elements.Book1
