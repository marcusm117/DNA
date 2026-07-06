import SystemE
import Book1.Prop34.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17_assumption1
    (f g k h : Point) (FG KH FK GH : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hfk_GH : f.sameSide k GH)
    (hpar_FG_KH : ¬FG.intersectsLine KH)
    (hpar_FK_GH : ¬FK.intersectsLine GH) :
    |(f─k)| = |(h─g)| ∧ ¬FK.intersectsLine GH := by
  have hpgram : formParallelogram f g k h FG KH FK GH :=
    ⟨hf_FG, hg_FG, hk_KH, hh_KH, hf_FK, hk_FK,
     ⟨hg_GH, hh_GH, hgh⟩, hfk_GH, hpar_FG_KH, hpar_FK_GH⟩
  euclid_apply (proposition_34' f g k h FG KH FK GH hpgram)
  constructor
  · euclid_finish
  · exact hpar_FK_GH

end Elements.Book1
