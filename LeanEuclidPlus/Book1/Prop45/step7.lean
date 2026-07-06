import SystemE
import Book1Variants.Prop29
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step7
    (f g k h : Point) (FK GH KH FG : Line)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hk_not_GH : ¬k.onLine GH)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hfk_GH : f.sameSide k GH)
    (hpar_FG_KH : ¬FG.intersectsLine KH)
    (hpar_FK_GH : ¬FK.intersectsLine GH) :
    ∠ f:k:h + ∠ k:h:g = ∟ + ∟ := by
  have hf_not_GH : ¬f.onLine GH := same_side_not_on_line f k GH hfk_GH
  have hFG_ne_KH : FG ≠ KH := by
    intro hFG_eq_KH
    have hh_FG : h.onLine FG := hFG_eq_KH.symm ▸ hh_KH
    have hFG_eq_GH : FG = GH := two_points_determine_line g h FG GH
      ⟨⟨hg_FG, hh_FG, hgh⟩, hg_GH, hh_GH⟩
    exact hf_not_GH (hFG_eq_GH ▸ hf_FG)
  have hfk : f ≠ k := fun heq =>
    absurd (intersection_lines_common_point k FG KH ⟨heq ▸ hf_FG, hk_KH, hFG_ne_KH⟩) hpar_FG_KH
  have hkh : k ≠ h := fun heq => hk_not_GH (heq ▸ hh_GH)
  have hdist_kf : distinctPointsOnLine k f FK := ⟨hk_FK, hf_FK, Ne.symm hfk⟩
  have hdist_hg : distinctPointsOnLine h g GH := ⟨hh_GH, hg_GH, Ne.symm hgh⟩
  have hdist_kh : distinctPointsOnLine k h KH := ⟨hk_KH, hh_KH, hkh⟩
  have hf_not_KH : ¬f.onLine KH := fun hf_KH =>
    hpar_FG_KH (intersection_lines_common_point f FG KH ⟨hf_FG, hf_KH, hFG_ne_KH⟩)
  have hfg_KH : f.sameSide g KH :=
    sameSide_of_parallel' f g f FG KH hf_FG hg_FG hf_FG hf_not_KH hpar_FG_KH
  euclid_apply (proposition_29''''' f g k h FK GH KH ⟨hdist_kf, hdist_hg, hdist_kh, hfg_KH, hpar_FK_GH⟩)

end Elements.Book1
