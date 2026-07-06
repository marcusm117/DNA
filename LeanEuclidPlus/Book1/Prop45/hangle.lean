import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle
    (e₁ e₂ e₃ : Point)
    (f g k h m l : Point)
    (FG KH FK GH : Line)
    (hk_KH : k.onLine KH)
    (hh_KH : h.onLine KH)
    (hk_FK : k.onLine FK)
    (hf_FK : f.onLine FK)
    (hh_GH : h.onLine GH)
    (hgh : g ≠ h)
    (hhkf_eq : ∠ h:k:f = ∠ e₁:e₂:e₃)
    (step9 : k.opposingSides m GH ∧ ∠ k:h:g + ∠ g:h:m = ∟ + ∟)
    (step17_assumption1 : |(f─k)| = |(h─g)| ∧ ¬FK.intersectsLine GH)
    (step18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    : ∠ f:k:m = ∠ e₁:e₂:e₃ := by
  -- Derive between k h m via pasch_4
  have hGH_ne_KH : GH ≠ KH := fun heq => step9.1.1 (heq ▸ hk_KH)
  have hkh : k ≠ h := fun heq => step9.1.1 (heq ▸ hh_GH)
  have hmh : m ≠ h := fun heq => step9.1.2.1 (heq ▸ hh_GH)
  have between_k_h_m : between k h m :=
    pasch_4 k h m GH KH ⟨hGH_ne_KH, hh_GH, hh_KH, step18.1, hkh, hmh, step9.1.2.2⟩
  -- Derive f ≠ k: if f = k then |(f─k)| = 0 = |(h─g)| → h = g, contradicting g ≠ h
  have hfk : f ≠ k := fun heq =>
    (Ne.symm hgh) (zero_segment_if h g
      (step17_assumption1.1.symm.trans (zero_segment_onlyif f k heq)))
  -- ¬between f k f: between_symm gives a ≠ c component, here a = c = f so f ≠ f → False
  have hnbff : ¬between f k f := fun hbtw =>
    (between_symm f k f hbtw).2.2.1 rfl
  -- ¬between h k m: from between k h m via between_symm
  have hnhkm : ¬between h k m := (between_symm k h m between_k_h_m).2.2.2
  -- equal_angles: both f endpoints on FK (same ray), h and m on KH (same ray from k)
  have hfkh_eq_fkm : ∠ f:k:h = ∠ f:k:m :=
    equal_angles k f f h m FK KH
      ⟨hk_FK, hf_FK, hf_FK, hk_KH, hh_KH, step18.1.2.1,
       hfk, hfk, Ne.symm hkh, Ne.symm step18.1.2.2, hnbff, hnhkm⟩
  -- angle_symm: ∠f:k:h = ∠h:k:f
  have hfkh_sym : ∠ f:k:h = ∠ h:k:f := angle_symm f k h ⟨hfk, hkh⟩
  exact hfkh_eq_fkm.symm.trans (hfkh_sym.trans hhkf_eq)

end Elements.Book1
