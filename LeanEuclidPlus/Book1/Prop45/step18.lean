import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step18
    (f g k h m l : Point) (FG GL GH KH HM LM : Line)
    (hk_KH : k.onLine KH)
    (hm_HM : m.onLine HM)
    (hf_FG : f.onLine FG)
    (hl_GL : l.onLine GL)
    (hl_LM : l.onLine LM)
    (hm_LM : m.onLine LM)
    (hfk_GH : f.sameSide k GH)
    (hh_sg_LM : h.sameSide g LM)
    (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (step10 : KH = HM)
    (step16 : FG = GL)
    (hpar_GH_LM : ¬GH.intersectsLine LM) :
    distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  have hm_KH : m.onLine KH := step10 ▸ hm_HM
  have hl_FG : l.onLine FG := step16 ▸ hl_GL
  have hkm : k ≠ m := by
    intro heq
    apply step9.1.2.2
    rw [← heq]
    exact same_side_rfl k GH step9.1.1
  have hf_not_GH : ¬f.onLine GH := same_side_not_on_line f k GH hfk_GH
  have hm_not_GH := step9.1.2.1
  have hGH_ne_LM : GH ≠ LM := fun heq => hm_not_GH (heq ▸ hm_LM)
  have hl_not_GH : ¬l.onLine GH := fun hl_GH =>
    hpar_GH_LM (intersection_lines_common_point l GH LM ⟨hl_GH, hl_LM, hGH_ne_LM⟩)
  have hpar_LM_GH : ¬LM.intersectsLine GH := fun hint =>
    hpar_GH_LM (intersection_symm LM GH hint)
  have hlm_sameSide : l.sameSide m GH :=
    sameSide_of_parallel' l m l LM GH hl_LM hm_LM hl_LM hl_not_GH hpar_LM_GH
  have hf_not_ss_l : ¬f.sameSide l GH := fun hfl =>
    step9.1.2.2 (same_side_trans f k m GH
      ⟨hfk_GH, same_side_trans l f m GH ⟨same_side_symm f l GH hfl, hlm_sameSide⟩⟩)
  have hfl : f ≠ l := by
    intro heq
    apply hf_not_ss_l
    rw [← heq]
    exact same_side_rfl f GH hf_not_GH
  exact ⟨⟨hk_KH, hm_KH, hkm⟩, ⟨hf_FG, hl_FG, hfl⟩⟩

end Elements.Book1
