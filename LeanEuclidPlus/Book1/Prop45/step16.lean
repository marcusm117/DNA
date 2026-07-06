import SystemE
import Book1.Prop14.Main
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step16
    (f g h k m l : Point) (FG GL GH LM : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hfk_GH : f.sameSide k GH)
    (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hl_LM : l.onLine LM) (hm_LM : m.onLine LM)
    (hh_sg_LM : h.sameSide g LM)
    (hpar_GH_LM : ¬GH.intersectsLine LM)
    (step15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟) :
    FG = GL := by
  have hf_not_GH : ¬f.onLine GH := same_side_not_on_line f k GH hfk_GH
  have hgf : g ≠ f := fun heq => hf_not_GH (heq ▸ hg_GH)
  have hg_not_LM : ¬g.onLine LM :=
    same_side_not_on_line g h LM (same_side_symm h g LM hh_sg_LM)
  have hgl : g ≠ l := fun heq => hg_not_LM (heq ▸ hl_LM)
  have hh_not_LM : ¬h.onLine LM := same_side_not_on_line h g LM hh_sg_LM
  have hGH_ne_LM : GH ≠ LM := fun heq => hh_not_LM (heq ▸ hh_GH)
  have hl_not_GH : ¬l.onLine GH := fun hl_GH =>
    hpar_GH_LM (intersection_lines_common_point l GH LM ⟨hl_GH, hl_LM, hGH_ne_LM⟩)
  have hpar_LM_GH : ¬LM.intersectsLine GH := fun hint =>
    hpar_GH_LM (intersection_symm LM GH hint)
  have hlm_sameSide : l.sameSide m GH :=
    sameSide_of_parallel' l m l LM GH hl_LM hm_LM hl_LM hl_not_GH hpar_LM_GH
  have hf_not_ss_l : ¬f.sameSide l GH := fun hfl =>
    step9.1.2.2 (same_side_trans f k m GH
      ⟨hfk_GH, same_side_trans l f m GH ⟨same_side_symm f l GH hfl, hlm_sameSide⟩⟩)
  have hf_opp_l : f.opposingSides l GH := ⟨hf_not_GH, hl_not_GH, hf_not_ss_l⟩
  euclid_apply (proposition_14 h g f l GH FG GL
    ⟨⟨hh_GH, hg_GH, Ne.symm hgh⟩, ⟨hg_FG, hf_FG, hgf⟩,
     ⟨hg_GL, hl_GL, hgl⟩, hf_opp_l, step15⟩)

end Elements.Book1
