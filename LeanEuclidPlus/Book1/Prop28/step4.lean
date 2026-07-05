import SystemE
import Book.Prop13
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_28_step4
    (a b d e f g h : Point) (AB EF : Line)
    (haonAB : a.onLine AB) (hbonAB : b.onLine AB) (hab : a ≠ b)
    (heonEF : e.onLine EF) (hfonEF : f.onLine EF) (hef : e ≠ f)
    (hbet_ab : between a g b)
    (hbet_eh : between e g h)
    (hbet_ghf : between g h f)
    (hsameside : b.sameSide d EF)
    (hassump1 : ∠ b:g:h + ∠ g:h:d = ∟ + ∟)
    (hassump2 : ∠ a:g:h + ∠ b:g:h = ∟ + ∟) :
    ∠ a:g:h + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d := by
  have hgf : between e g f := between_trans_out e g h f ⟨hbet_eh, hbet_ghf⟩
  have hgonEF : g.onLine EF := between_same_line_in e g f EF ⟨hgf, heonEF, hfonEF⟩
  have hhonEF : h.onLine EF := between_same_line_out e g h EF ⟨hbet_eh, heonEF, hgonEF⟩
  have hgonAB : g.onLine AB := between_same_line_in a g b AB ⟨hbet_ab, haonAB, hbonAB⟩
  have hnbonEF : ¬b.onLine EF := same_side_not_on_line b d EF hsameside
  have hne : EF ≠ AB := by intro heq; exact hnbonEF (heq ▸ hbonAB)
  have hdEFhg : distinctPointsOnLine h g EF := ⟨hhonEF, hgonEF, by euclid_finish⟩
  have hdABab : distinctPointsOnLine a b AB := ⟨haonAB, hbonAB, hab⟩
  euclid_apply (proposition_13 h g a b EF AB)
  linarith

end Elements.Book1
