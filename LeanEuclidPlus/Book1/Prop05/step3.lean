import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step3 (c f b g : Point) (FC GB : Line)
    (h1 : c.onLine FC) (h2 : f.onLine FC) (h3 : b.onLine GB) (h4 : g.onLine GB) :
    c.onLine FC ∧ f.onLine FC ∧ b.onLine GB ∧ g.onLine GB :=
  ⟨h1, h2, h3, h4⟩

end Elements.Book1
