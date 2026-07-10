import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step2
    (ABC : Circle) (d e f g h k l : Point) (GK HL : Line)
    (he_GK : e.onLine GK) (hd_GK : d.onLine GK)
    (hg_ABC : g.onCircle ABC) (hg_GK : g.onLine GK)
    (hk_ABC : k.onCircle ABC) (hk_GK : k.onLine GK)
    (hf_HL : f.onLine HL) (hd_HL : d.onLine HL)
    (hh_ABC : h.onCircle ABC) (hh_HL : h.onLine HL)
    (hl_ABC : l.onCircle ABC) (hl_HL : l.onLine HL)
    : (e.onLine GK ∧ d.onLine GK) ∧
      (g.onCircle ABC ∧ g.onLine GK) ∧ (k.onCircle ABC ∧ k.onLine GK) ∧
      (f.onLine HL ∧ d.onLine HL) ∧
      (h.onCircle ABC ∧ h.onLine HL) ∧ (l.onCircle ABC ∧ l.onLine HL) := by
  exact ⟨⟨he_GK, hd_GK⟩, ⟨hg_ABC, hg_GK⟩, ⟨hk_ABC, hk_GK⟩, ⟨hf_HL, hd_HL⟩, ⟨hh_ABC, hh_HL⟩, ⟨hl_ABC, hl_HL⟩⟩

end Elements.Book3
