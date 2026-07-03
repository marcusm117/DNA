import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step6
  (c' e f : Point) (DE EF DF EG GF : Line)
  (ptImg : Point → Point)
  (h_ptImg_c : ptImg c = c')
  (he_EG : e.onLine EG) (he_DE : e.onLine DE)
  (hc'_GF : c'.onLine GF) (hf_DF : f.onLine DF)
  (step1 : ptImg c = f)
  : (e.onLine EG ∧ e.onLine DE) ∧ f.onLine GF ∧ f.onLine DF := by
  have hcf : c' = f := by rw [← h_ptImg_c]; exact step1
  clear step1 h_ptImg_c ptImg
  exact ⟨⟨he_EG, he_DE⟩, hcf ▸ hc'_GF, hf_DF⟩

end Elements.Book1
