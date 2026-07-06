import SystemE
import Book1.Prop29.variants
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step11
    (f g k h m : Point) (FG GH KH HM : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hfk_GH : f.sameSide k GH)
    (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (step10 : KH = HM)
    (hassump1 : ¬(FG.intersectsLine KH)) :
    ∠ m:h:g = ∠ h:g:f := by
  have hf_not_GH : ¬f.onLine GH := same_side_not_on_line f k GH hfk_GH
  have hfg : f ≠ g := fun heq => hf_not_GH (heq ▸ hg_GH)
  have hhm : h ≠ m := fun heq => step9.1.2.1 (heq ▸ hh_GH)
  have hf_not_ss_m : ¬f.sameSide m GH := fun hfm =>
    step9.1.2.2 (same_side_symm m k GH (same_side_trans f m k GH ⟨hfm, hfk_GH⟩))
  have hf_opp_m_GH : f.opposingSides m GH :=
    ⟨hf_not_GH, step9.1.2.1, hf_not_ss_m⟩
  have hpar_FG_HM : ¬FG.intersectsLine HM := step10 ▸ hassump1
  have hdist_fg_FG : distinctPointsOnLine f g FG := ⟨hf_FG, hg_FG, hfg⟩
  have hdist_hm_HM : distinctPointsOnLine h m HM := ⟨hh_HM, hm_HM, hhm⟩
  have hdist_gh_GH : distinctPointsOnLine g h GH := ⟨hg_GH, hh_GH, hgh⟩
  have hprop29 : ∠ f:g:h = ∠ g:h:m := by
    euclid_apply (proposition_29''' f m g h FG HM GH ⟨hdist_fg_FG, hdist_hm_HM, hdist_gh_GH, hf_opp_m_GH, hpar_FG_HM⟩)
  have hangle_fgh : ∠ f:g:h = ∠ h:g:f := angle_symm f g h ⟨hfg, hgh⟩
  have hangle_ghm : ∠ g:h:m = ∠ m:h:g := angle_symm g h m ⟨hgh, hhm⟩
  linarith

end Elements.Book1
