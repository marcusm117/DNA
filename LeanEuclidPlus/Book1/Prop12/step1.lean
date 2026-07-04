import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step1 (d c : Point) (AB : Line)
    (h1 : ¬d.onLine AB) (h2 : ¬c.onLine AB) (h3 : ¬d.sameSide c AB) :
    d.opposingSides c AB := by
  exact ⟨h1, h2, h3⟩

end Elements.Book1
