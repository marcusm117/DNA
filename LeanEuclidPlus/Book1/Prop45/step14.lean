import SystemE
import Book.Prop29
import Helpers.SameSide
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step14
    (g h m l : Point) (GL HM GH LM : Line)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hl_LM : l.onLine LM) (hm_LM : m.onLine LM)
    (hm_not_GH : ¬m.onLine GH)
    (hh_sg_LM : h.sameSide g LM)
    (hpar_HM_GL : ¬HM.intersectsLine GL)
    (hpar_GH_LM : ¬GH.intersectsLine LM) :
    ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  have hg_not_LM : ¬g.onLine LM :=
    same_side_not_on_line g h LM (same_side_symm h g LM hh_sg_LM)
  have hgl : g ≠ l := fun heq => hg_not_LM (heq ▸ hl_LM)
  have hhm : h ≠ m := fun heq => hm_not_GH (heq ▸ hh_GH)
  have hl_not_GH : ¬l.onLine GH := by
    intro hl_GH
    have hGH_ne_LM : GH ≠ LM := fun heq =>
      same_side_not_on_line h g LM hh_sg_LM (heq ▸ hh_GH)
    exact hpar_GH_LM (intersection_lines_common_point l GH LM ⟨hl_GH, hl_LM, hGH_ne_LM⟩)
  have hpar_LM_GH : ¬LM.intersectsLine GH := fun hint =>
    hpar_GH_LM (intersection_symm LM GH hint)
  have hlm_sameSide : l.sameSide m GH :=
    sameSide_of_parallel' l m l LM GH hl_LM hm_LM hl_LM hl_not_GH hpar_LM_GH
  have hpar_GL_HM : ¬GL.intersectsLine HM := fun hint =>
    hpar_HM_GL (intersection_symm GL HM hint)
  have hdist_gl : distinctPointsOnLine g l GL := ⟨hg_GL, hl_GL, hgl⟩
  have hdist_hm : distinctPointsOnLine h m HM := ⟨hh_HM, hm_HM, hhm⟩
  have hdist_gh : distinctPointsOnLine g h GH := ⟨hg_GH, hh_GH, hgh⟩
  have hprop29 : ∠ l:g:h + ∠ g:h:m = ∟ + ∟ := by
    euclid_apply (proposition_29''''' l m g h GL HM GH ⟨hdist_gl, hdist_hm, hdist_gh, hlm_sameSide, hpar_GL_HM⟩)
  have hangle_lgh : ∠ l:g:h = ∠ h:g:l := angle_symm l g h ⟨Ne.symm hgl, hgh⟩
  have hangle_ghm : ∠ g:h:m = ∠ m:h:g := angle_symm g h m ⟨hgh, hhm⟩
  linarith

end Elements.Book1
