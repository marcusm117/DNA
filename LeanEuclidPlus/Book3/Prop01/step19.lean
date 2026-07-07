import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step19 (ABC : Circle) (f : Point)
    (step18 : ∀ (g' : Point), g' ≠ f → ¬g'.isCentre ABC) :
    f.isCentre ABC := by
  obtain ⟨k, hk⟩ := exists_centre ABC
  by_cases hkf : k = f
  · rw [← hkf]; exact hk
  · exact absurd hk (step18 k hkf)

end Elements.Book3
