import SystemE
import Book1.Prop14.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step10
    (g k h m : Point) (GH KH HM : Line)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hm_HM : m.onLine HM) (hh_HM : h.onLine HM)
    (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟)) :
    KH = HM := by
  have hk_not_GH : ¬k.onLine GH := step9.1.1
  have hm_not_GH : ¬m.onLine GH := step9.1.2.1
  have hhk : h ≠ k := fun heq => hk_not_GH (heq ▸ hh_GH)
  have hhm : h ≠ m := fun heq => hm_not_GH (heq ▸ hh_GH)
  have hdist_gh : distinctPointsOnLine g h GH := ⟨hg_GH, hh_GH, hgh⟩
  have hdist_hk : distinctPointsOnLine h k KH := ⟨hh_KH, hk_KH, hhk⟩
  have hdist_hm : distinctPointsOnLine h m HM := ⟨hh_HM, hm_HM, hhm⟩
  have hangle_gk : ∠ g:h:k = ∠ k:h:g := angle_symm g h k ⟨hgh, hhk⟩
  have hangle_sum : ∠ g:h:k + ∠ g:h:m = ∟ + ∟ := by linarith [step9.2]
  euclid_apply (proposition_14 g h k m GH KH HM ⟨hdist_gh, hdist_hk, hdist_hm, step9.1, hangle_sum⟩)

end Elements.Book1
