import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step5 (a b e f : Point) (EF AB : Line)
    (hefne : e ≠ f)
    (he_onEF : e.onLine EF)
    (hf_onEF : f.onLine EF)
    (habne : a ≠ b)
    (ha_onAB : a.onLine AB)
    (hb_onAB : b.onLine AB) :
    distinctPointsOnLine e f EF ∧ distinctPointsOnLine a b AB := by
  exact ⟨⟨he_onEF, hf_onEF, hefne⟩, ⟨ha_onAB, hb_onAB, habne⟩⟩

end Elements.Book3
