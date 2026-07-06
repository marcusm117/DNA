import SystemE
import Book.Prop33
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19
    (f g k h m l : Point) (FK FG GL GH KH LM : Line)
    (hf_FG : f.onLine FG)
    (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH)
    (hh_KH : h.onLine KH)
    (hg_GH : g.onLine GH)
    (hh_GH : h.onLine GH)
    (hk_FK : k.onLine FK)
    (hf_FK : f.onLine FK)
    (hgh : g ≠ h)
    (hfk_GH : f.sameSide k GH)
    (step11_assumption1 : ¬FG.intersectsLine KH)
    (step17 : |(k─f)| = |(m─l)| ∧ ¬FK.intersectsLine LM)
    (step18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml : m ≠ l) :
    |(k─m)| = |(f─l)| ∧ ¬KH.intersectsLine FG := by
  have hkf : k ≠ f := by
    intro heq
    have hkf_zero : |(k─f)| = 0 := zero_segment_onlyif k f heq
    rw [step17.1] at hkf_zero
    exact hml (zero_segment_if m l hkf_zero)
  have hf_not_GH : ¬f.onLine GH := same_side_not_on_line f k GH hfk_GH
  have hh_not_FG : ¬h.onLine FG := by
    intro hh_FG
    have hFG_GH := two_points_determine_line g h FG GH ⟨⟨hg_FG, hh_FG, hgh⟩, hg_GH, hh_GH⟩
    exact hf_not_GH (hFG_GH ▸ hf_FG)
  have hKH_ne_FG : KH ≠ FG := fun heq => hh_not_FG (heq ▸ hh_KH)
  have hk_not_FG : ¬k.onLine FG := fun hk_FG =>
    step11_assumption1 (intersection_lines_common_point k FG KH ⟨hk_FG, hk_KH, Ne.symm hKH_ne_FG⟩)
  have hpar_KH_FG : ¬KH.intersectsLine FG := fun hint =>
    step11_assumption1 (intersection_symm KH FG hint)
  have hkm_ss_FG : k.sameSide m FG :=
    sameSide_of_parallel' k m k KH FG step18.1.1 step18.1.2.1 step18.1.1 hk_not_FG hpar_KH_FG
  euclid_apply (proposition_33 k f m l FK LM KH FG
    ⟨⟨hk_FK, hf_FK, hkf⟩, ⟨hm_LM, hl_LM, hml⟩,
     step18.1, step18.2, hkm_ss_FG, step17.2, step17.1⟩)
  (try split_ands) <;> assumption

end Elements.Book1
