import SystemE
import Book1.Prop30.Main
import Book1.Prop34.variants
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17
    (f g k h m l : Point) (FK FG GL GH LM KH : Line)
    (hf_FK : f.onLine FK)
    (hf_FG : f.onLine FG)
    (hg_FG : g.onLine FG)
    (hl_GL : l.onLine GL)
    (hg_GH : g.onLine GH)
    (hm_LM : m.onLine LM)
    (hl_LM : l.onLine LM)
    (hm_not_GH : ¬m.onLine GH)
    (hfk_GH : f.sameSide k GH)
    (hh_sg_LM : h.sameSide g LM)
    (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (step16 : FG = GL)
    (hassump1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
    (hassump2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hk_FK : k.onLine FK) (hh_GH : h.onLine GH)
    (hgh : g ≠ h) (hpar_FG_KH : ¬FG.intersectsLine KH) :
    |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  -- Criterion-3 [Prop.~1.34]: cite proposition_34 explicitly in this cone
  have hpgram_fgkh : formParallelogram f g k h FG KH FK GH :=
    ⟨hf_FG, hg_FG, hk_KH, hh_KH, hf_FK, hk_FK,
     ⟨hg_GH, hh_GH, hgh⟩, hfk_GH, hpar_FG_KH, hassump1.2⟩
  have _h34 : |(f─k)| = |(h─g)| ∧ ¬FK.intersectsLine GH := by
    euclid_apply (proposition_34' f g k h FG KH FK GH hpgram_fgkh)
    constructor
    · euclid_finish
    · assumption
  have hf_not_GH : ¬f.onLine GH := same_side_not_on_line f k GH hfk_GH
  have hFK_ne_GH : FK ≠ GH := fun heq => hf_not_GH (heq ▸ hf_FK)
  have hLM_ne_GH : LM ≠ GH := fun heq => hm_not_GH (heq ▸ hm_LM)
  have hg_not_LM : ¬g.onLine LM :=
    same_side_not_on_line g h LM (same_side_symm h g LM hh_sg_LM)
  have hGH_ne_LM : GH ≠ LM := fun heq => hg_not_LM (heq ▸ hg_GH)
  have hpar_LM_GH : ¬LM.intersectsLine GH := fun hint =>
    hassump2.2 (intersection_symm LM GH hint)
  have hl_FG : l.onLine FG := step16 ▸ hl_GL
  have hg_not_FK : ¬g.onLine FK := fun hg_FK =>
    hassump1.2 (intersection_lines_common_point g FK GH ⟨hg_FK, hg_GH, hFK_ne_GH⟩)
  have hl_not_GH : ¬l.onLine GH := fun hl_GH =>
    hassump2.2 (intersection_lines_common_point l GH LM ⟨hl_GH, hl_LM, hGH_ne_LM⟩)
  have hlm_sameSide : l.sameSide m GH :=
    sameSide_of_parallel' l m l LM GH hl_LM hm_LM hl_LM hl_not_GH hpar_LM_GH
  have hf_not_ss_l : ¬f.sameSide l GH := fun hfl =>
    step9.1.2.2 (same_side_trans f k m GH
      ⟨hfk_GH, same_side_trans l f m GH ⟨same_side_symm f l GH hfl, hlm_sameSide⟩⟩)
  have hfl : f ≠ l := by
    intro heq
    apply hf_not_ss_l
    rw [← heq]
    exact same_side_trans k f f GH ⟨same_side_symm f k GH hfk_GH, same_side_symm f k GH hfk_GH⟩
  have hFK_ne_LM : FK ≠ LM := by
    intro heq
    have hl_FK : l.onLine FK := heq ▸ hl_LM
    have hFK_FG : FK = FG :=
      two_points_determine_line f l FK FG ⟨⟨hf_FK, hl_FK, hfl⟩, hf_FG, hl_FG⟩
    exact hg_not_FK (hFK_FG ▸ hg_FG)
  have hpar_FK_LM : ¬FK.intersectsLine LM := by
    euclid_apply (proposition_30 FK LM GH
      ⟨hFK_ne_LM, hLM_ne_GH, Ne.symm hFK_ne_GH, hassump1.2, hpar_LM_GH⟩)
  exact ⟨(segment_symmetric k f).trans (hassump1.1.trans hassump2.1), hpar_FK_LM⟩

end Elements.Book1
