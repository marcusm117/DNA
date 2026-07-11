import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pure-logic proof: given ¬e.onLine FG as hypothesis, all three line-distinctness facts
-- follow from h_e_off_fg alone; two_points_determine_line closes the EG≠FE case.
-- h_e_off_fg is backed by step11_assumption2_e_off_fg (currently @euclid_gap, needs the
-- degenerate-angle axiom ∀a b, ∠a:b:b = 0 in System E before it can be proved).

theorem helper_3_15_step11_assumption2_tri_efg
    (e f g : Point)
    (FE FG EG : Line)
    (hf_FE : f.onLine FE) (he_FE : e.onLine FE)
    (he_EG : e.onLine EG) (hg_EG : g.onLine EG)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hfg : f ≠ g)
    (h_e_off_fg : ¬e.onLine FG) :
    formTriangle e f g FE FG EG := by
  have he_ne_f : e ≠ f := fun h => h_e_off_fg (h ▸ hf_FG)
  have hFE_ne_FG : FE ≠ FG := fun h => h_e_off_fg (h ▸ he_FE)
  have hFG_ne_EG : FG ≠ EG := fun h => h_e_off_fg (h.symm ▸ he_EG)
  have hEG_ne_FE : EG ≠ FE := by
    intro h
    have hg_FE : g.onLine FE := h ▸ hg_EG
    -- distinctPointsOnLine g f FE = ⟨g.onLine FE, f.onLine FE, g ≠ f⟩
    have hFE_eq_FG := two_points_determine_line g f FE FG
      ⟨⟨hg_FE, hf_FE, hfg.symm⟩, hg_FG, hf_FG⟩
    exact hFE_ne_FG hFE_eq_FG
  -- distinctPointsOnLine e f FE = ⟨e.onLine FE, f.onLine FE, e ≠ f⟩
  exact ⟨⟨he_FE, hf_FE, he_ne_f⟩, hf_FG, hg_FG, hg_EG, he_EG, hFE_ne_FG, hFG_ne_EG, hEG_ne_FE⟩

end Elements.Book3
