import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step6
    (f k h g m : Point) (FG KH GH : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH)
    (hfk_GH : f.sameSide k GH) (hg_ne_h : g ≠ h)
    (hpar_FG_KH : ¬FG.intersectsLine KH)
    (step5 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g) :
    ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by
  have hf_not_GH : ¬f.onLine GH := same_side_not_on_line f k GH hfk_GH
  have hk_not_GH : ¬k.onLine GH := same_side_not_on_line k f GH (same_side_symm f k GH hfk_GH)
  have hFG_ne_KH : FG ≠ KH := by
    intro hFG_eq_KH
    have hh_FG : h.onLine FG := hFG_eq_KH.symm ▸ hh_KH
    have hFG_eq_GH : FG = GH := two_points_determine_line g h FG GH
      ⟨⟨hg_FG, hh_FG, hg_ne_h⟩, hg_GH, hh_GH⟩
    exact hf_not_GH (hFG_eq_GH ▸ hf_FG)
  have hfk : f ≠ k := fun heq =>
    absurd (intersection_lines_common_point k FG KH ⟨heq ▸ hf_FG, hk_KH, hFG_ne_KH⟩) hpar_FG_KH
  have hkh : k ≠ h := fun heq => hk_not_GH (heq ▸ hh_GH)
  have hfkh : ∠ f:k:h = ∠ h:k:f := angle_symm f k h ⟨hfk, hkh⟩
  linarith

end Elements.Book1
