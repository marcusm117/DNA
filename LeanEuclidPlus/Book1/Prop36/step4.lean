import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step4 (b c e h : Point) (BE CH : Line)
  (h_step1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH) :
  distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by
  obtain ⟨⟨hbBE, heBE, hne1⟩, ⟨hcCH, hhCH, hne2⟩⟩ := h_step1
  exact ⟨⟨heBE, hbBE, hne1.symm⟩, ⟨hhCH, hcCH, hne2.symm⟩⟩

end Elements.Book1
