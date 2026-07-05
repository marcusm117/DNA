import SystemE
import Book1.Prop28.step1
import Book1.Prop28.step2
import Book1.Prop28.step3
import Book1.Prop28.step4
import Book1.Prop28.step5
import Book1.Prop28.step6
import Book1.Prop28.step7
import Book1.Prop28.step8
import Book1.Prop28.step1_assumption2
import Book1.Prop28.step4_assumption2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_28 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧
  (∠ e:g:b = ∠ g:h:d ∨ ∠ b:g:h + ∠ g:h:d = ∟ + ∟) →
  ¬(AB.intersectsLine CD) := by
  euclid_intros
  euclid_intro_sentence "1.28.0"
    "If a straight-line falling across two straight-lines makes the external angle equal to the internal and opposite angle on the same side, or (makes) the (sum  of the) internal (angles) on the same side equal to two right-angles, then the (two) straight-lines will be parallel to one another.   For let $EF$, falling across the two straight-lines $AB$ and $CD$, make the external angle $EGB$ equal to the internal and opposite angle $GHD$, or the (sum of the) internal (angles) on the same side, $BGH$ and $GHD$, equal to two right-angles. I say that $AB$ is parallel to $CD$. "
  have h_or : ∠ e:g:b = ∠ g:h:d ∨ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by assumption
  rcases h_or with h1 | h2
  ·
    -- @assumption_valid
    have step1_assumption1 : ∠ e:g:b = ∠ g:h:d := by assumption
    -- @assumption_gap
    have step1_assumption2 : ∠ e:g:b = ∠ a:g:h := by euclid_apply (helper_1_28_step1_assumption2 a b d e f g h AB EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)))
    -- @assumption ("$EGB$ is equal to $GHD$", ∠ e:g:b = ∠ g:h:d)
    -- @assumption ("$EGB$ is equal to $AGH$ [Prop.~1.15]", ∠ e:g:b = ∠ a:g:h)
    euclid_sentence "1.28.1"
      "For since (in the first case) $EGB$ is equal to $GHD$, but $EGB$ is equal to $AGH$ [Prop.~1.15], $AGH$ is thus also equal to $GHD$."
      (step1 : ∠ a:g:h = ∠ g:h:d) := by euclid_apply (helper_1_28_step1 a b d e f g h AB EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)) (by euclid_assumption "$EGB$ is equal to $GHD$" (show ∠ e:g:b = ∠ g:h:d; assumption)) (by euclid_assumption "$EGB$ is equal to $AGH$ [Prop.~1.15]" (show ∠ e:g:b = ∠ a:g:h; assumption)))
    euclid_sentence "1.28.2"
      "And they are alternate (angles)."
      (step2 : a.opposingSides d EF) := by euclid_apply (helper_1_28_step2 a b d e f g h EF (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)))
    euclid_sentence "1.28.3"
      "Thus, $AB$ is  parallel to $CD$ [Prop.~1.27].  "
      (step3 : ¬(AB.intersectsLine CD)) := by euclid_apply (helper_1_28_step3 a b c d e f g h AB CD EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between c h d; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show ∠ a:g:h = ∠ g:h:d; assumption)) (by euclid_assumption "" (show a.opposingSides d EF; assumption)))
    exact step3 (by assumption)
  ·
    -- @assumption_valid
    have step4_assumption1 : ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by assumption
    -- @assumption_gap
    have step4_assumption2 : ∠ a:g:h + ∠ b:g:h = ∟ + ∟ := by euclid_apply (helper_1_28_step4_assumption2 a b d e f g h AB EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)))
    -- @assumption ("$BGH$ and $GHD$ is equal to two right-angles", ∠ b:g:h + ∠ g:h:d = ∟ + ∟)
    -- @assumption ("$AGH$ and $BGH$ is also equal to two right-angles [Prop.~1.13]", ∠ a:g:h + ∠ b:g:h = ∟ + ∟)
    euclid_sentence "1.28.4"
      "Again, since (in the second case, the sum of) $BGH$ and $GHD$ is equal to two right-angles,  and (the sum of) $AGH$ and $BGH$ is also equal to two right-angles [Prop.~1.13],  (the sum of) $AGH$ and $BGH$ is thus equal to (the sum of) $BGH$ and $GHD$."
      (step4 : ∠ a:g:h + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d) := by euclid_apply (helper_1_28_step4 a b d e f g h AB EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)) (by euclid_assumption "$BGH$ and $GHD$ is equal to two right-angles" (show ∠ b:g:h + ∠ g:h:d = ∟ + ∟; assumption)) (by euclid_assumption "$AGH$ and $BGH$ is also equal to two right-angles [Prop.~1.13]" (show ∠ a:g:h + ∠ b:g:h = ∟ + ∟; assumption)))
    euclid_sentence "1.28.5"
      "Let $BGH$ have been subtracted from both."
      (step5 : ∠ a:g:h + ∠ b:g:h - ∠ b:g:h = ∠ b:g:h + ∠ g:h:d - ∠ b:g:h) := by euclid_apply (helper_1_28_step5 (by euclid_assumption "" (show ∠ a:g:h + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d; assumption)))
    euclid_sentence "1.28.6"
      "Thus, the remainder $AGH$ is equal to the remainder $GHD$."
      (step6 : ∠ a:g:h = ∠ g:h:d) := by euclid_apply (helper_1_28_step6 (by euclid_assumption "" (show ∠ a:g:h + ∠ b:g:h - ∠ b:g:h = ∠ b:g:h + ∠ g:h:d - ∠ b:g:h; assumption)))
    euclid_sentence "1.28.7"
      "And they are alternate (angles)."
      (step7 : a.opposingSides d EF) := by euclid_apply (helper_1_28_step7 a b d e f g h EF (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)))
    euclid_sentence "1.28.8"
      "Thus, $AB$ is parallel to $CD$ [Prop.~1.27]. "
      (step8 : ¬(AB.intersectsLine CD)) := by euclid_apply (helper_1_28_step8 a b c d e f g h AB CD EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between c h d; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show ∠ a:g:h = ∠ g:h:d; assumption)) (by euclid_assumption "" (show a.opposingSides d EF; assumption)))
    exact step8 (by assumption)
  euclid_conclude_sentence "1.28.9"
    "Thus, if a straight-line falling across  two straight-lines makes the external angle equal to the internal and opposite angle on the same side, or (makes) the (sum of the) internal (angles) on the same side equal to two right-angles, then the (two) straight-lines will be parallel (to one another). (Which is) the very thing it was required to show."

end Elements.Book1
