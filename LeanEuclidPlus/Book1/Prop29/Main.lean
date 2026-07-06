import SystemE
import Book1.Prop13.Main
import Book1.Prop15.Main
import Book1.Prop29.step1
import Book1.Prop29.step2
import Book1.Prop29.step3
import Book1.Prop29.step4
import Book1.Prop29.step5
import Book1.Prop29.step6
import Book1.Prop29.step7
import Book1.Prop29.step8
import Book1.Prop29.step9
import Book1.Prop29.step10
import Book1.Prop29.step11
import Book1.Prop29.step12
import Book1.Prop29.step13
import Book1.Prop29.step14
import Book1.Prop29.step15
import Book1.Prop29.step16
import Book1.Prop29.step17
import Book1.Prop29.hreduction
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_29 : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD)
  → ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by
  euclid_intros
  euclid_intro_sentence "1.29.0"
    "A straight-line falling across  parallel straight-lines makes the alternate angles equal to one another,  the external (angle) equal to the internal and opposite (angle), and the (sum of the) internal (angles) on the same side equal to two right-angles.   For let the straight-line $EF$ fall across the parallel straight-lines $AB$ and $CD$. I say that it makes the  alternate angles, $AGH$ and $GHD$,  equal,  the external angle $EGB$ equal to the internal and opposite (angle) $GHD$, and the (sum of the) internal (angles) on the same side, $BGH$ and $GHD$, equal to two right-angles. "

  -- Euclid argues by contradiction: suppose AGH ≠ GHD; the case (AGH > GHD) is absurd; the other is symmetric.
  have habsurd : ¬(∠ a:g:h ≠ ∠ g:h:d) := by
    intro hne
    -- @assumption_valid
    have step1_assumption1 : ∠ a:g:h ≠ ∠ g:h:d := by assumption
    -- @assumption ("$AGH$ is unequal to $GHD$", ∠ a:g:h ≠ ∠ g:h:d)
    euclid_sentence "1.29.1"
      "For if $AGH$ is unequal to $GHD$ then one of them is greater."
      (step1 : ∠ a:g:h ≠ ∠ g:h:d → ∠ a:g:h > ∠ g:h:d ∨ ∠ g:h:d > ∠ a:g:h) := by euclid_apply (helper_1_29_step1 (by euclid_assumption "$AGH$ is unequal to $GHD$" (show ∠ a:g:h ≠ ∠ g:h:d; assumption)))
    -- Euclid writes only the AGH > GHD case; the other is symmetric (wlog).
    wlog hgt : ∠ a:g:h > ∠ g:h:d generalizing a b c d g h AB CD with Hsym
    -- symmetric case (Phase B: swapped-figure helper)
    · have hreduction : False := by euclid_apply (helper_1_29_hreduction a b c d e f g h AB CD EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between c h d; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show ∠ a:g:h ≠ ∠ g:h:d; assumption)) (by euclid_assumption "" (show ¬∠ a:g:h > ∠ g:h:d; assumption)) (by euclid_assumption "" (show ∠ a:g:h ≠ ∠ g:h:d → ∠ a:g:h > ∠ g:h:d ∨ ∠ g:h:d > ∠ a:g:h; assumption)))
      exact hreduction
    -- Euclid's case: AGH is the greater
    ·
      euclid_sentence "1.29.2"
        "Let $AGH$ be greater."
        (step2 : ∠ a:g:h > ∠ g:h:d) := by euclid_apply (helper_1_29_step2 (by euclid_assumption "" (show ∠ a:g:h > ∠ g:h:d; assumption)))
      euclid_sentence "1.29.3"
        "Let $BGH$ have been added to both."
        (step3 : ∠ a:g:h > ∠ g:h:d → ∠ a:g:h + ∠ b:g:h > ∠ g:h:d + ∠ b:g:h) := by euclid_apply (helper_1_29_step3 )
      euclid_sentence "1.29.4"
        "Thus, (the sum of) $AGH$ and $BGH$ is greater than (the sum of) $BGH$ and $GHD$."
        (step4 : ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d) := by euclid_apply (helper_1_29_step4 (by euclid_assumption "" (show ∠ a:g:h > ∠ g:h:d; assumption)) (by euclid_assumption "" (show ∠ a:g:h > ∠ g:h:d → ∠ a:g:h + ∠ b:g:h > ∠ g:h:d + ∠ b:g:h; assumption)))
      euclid_sentence "1.29.5"
        "But, (the sum of) $AGH$ and $BGH$ is equal to two right-angles [Prop~1.13]."
        (step5 : ∠ a:g:h + ∠ b:g:h = ∟ + ∟) := by euclid_apply (helper_1_29_step5 a b c d e f g h AB CD EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between c h d; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)))
      euclid_sentence "1.29.6"
        "Thus,  (the sum of) $BGH$ and $GHD$ is [also] less than two right-angles. "
        (step6 : ∠ b:g:h + ∠ g:h:d < ∟ + ∟) := by euclid_apply (helper_1_29_step6 (by euclid_assumption "" (show ∠ a:g:h + ∠ b:g:h > ∠ b:g:h + ∠ g:h:d; assumption)) (by euclid_assumption "" (show ∠ a:g:h + ∠ b:g:h = ∟ + ∟; assumption)))
      euclid_sentence "1.29.7"
        "But (straight-lines) being produced to infinity from (internal angles whose sum is) less than two right-angles meet together [Post.~5]."
        (step7 : ∠ b:g:h + ∠ g:h:d < ∟ + ∟ → AB.intersectsLine CD) := by euclid_apply (helper_1_29_step7 a b c d e f g h AB CD EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between c h d; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)) (by euclid_assumption "" (show ∠ b:g:h + ∠ g:h:d < ∟ + ∟; assumption)))
      euclid_sentence "1.29.8"
        "Thus, $AB$ and $CD$, being produced to infinity, will meet together."
        (step8 : AB.intersectsLine CD) := by euclid_apply (helper_1_29_step8 AB CD (by euclid_assumption "" (show ∠ b:g:h + ∠ g:h:d < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ b:g:h + ∠ g:h:d < ∟ + ∟ → AB.intersectsLine CD; assumption)))
      -- @assumption_valid
      have step9_assumption1 : ¬(AB.intersectsLine CD) := by assumption
      -- @assumption ("them (initially) being assumed parallel (to one another)", ¬(AB.intersectsLine CD))
      euclid_sentence "1.29.9"
        "But they do not meet, on account of them (initially) being assumed parallel (to one another) [Def.~1.23]."
        (step9 : False) := by euclid_apply (helper_1_29_step9 AB CD (by euclid_assumption "" (show AB.intersectsLine CD; assumption)) (by euclid_assumption "them (initially) being assumed parallel (to one another)" (show ¬(AB.intersectsLine CD); assumption)))
      exact step9
  euclid_sentence "1.29.10"
    "Thus, $AGH$ is not unequal to $GHD$."
    (step10 : ¬(∠ a:g:h ≠ ∠ g:h:d)) := by euclid_apply (helper_1_29_step10 (by euclid_assumption "" (show ¬(∠ a:g:h ≠ ∠ g:h:d); assumption)))
  euclid_sentence "1.29.11"
    "Thus, (it is) equal."
    (step11 : ∠ a:g:h = ∠ g:h:d) := by euclid_apply (helper_1_29_step11 (by euclid_assumption "" (show ¬(∠ a:g:h ≠ ∠ g:h:d); assumption)))
  euclid_sentence "1.29.12"
    "But, $AGH$ is equal to $EGB$ [Prop.~1.15]. "
    (step12 : ∠ a:g:h = ∠ e:g:b) := by euclid_apply (helper_1_29_step12 a b c d e f g h AB CD EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between c h d; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)))
  euclid_sentence "1.29.13"
    "And $EGB$ is thus also equal to $GHD$."
    (step13 : ∠ e:g:b = ∠ g:h:d) := by euclid_apply (helper_1_29_step13 (by euclid_assumption "" (show ∠ a:g:h = ∠ g:h:d; assumption)) (by euclid_assumption "" (show ∠ a:g:h = ∠ e:g:b; assumption)))
  euclid_sentence "1.29.14"
    "Let $BGH$ be added to both."
    (step14 : ∠ e:g:b = ∠ g:h:d → ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d) := by euclid_apply (helper_1_29_step14 )
  euclid_sentence "1.29.15"
    "Thus, (the sum of) $EGB$ and $BGH$ is equal to (the sum of) $BGH$ and $GHD$."
    (step15 : ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d) := by euclid_apply (helper_1_29_step15 (by euclid_assumption "" (show ∠ e:g:b = ∠ g:h:d; assumption)) (by euclid_assumption "" (show ∠ e:g:b = ∠ g:h:d → ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d; assumption)))
  euclid_sentence "1.29.16"
    "But, (the sum of) $EGB$ and $BGH$ is equal to two right-angles [Prop.~1.13]. "
    (step16 : ∠ e:g:b + ∠ b:g:h = ∟ + ∟) := by euclid_apply (helper_1_29_step16 a b c d e f g h AB CD EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show between c h d; assumption)) (by euclid_assumption "" (show between e g h; assumption)) (by euclid_assumption "" (show between g h f; assumption)) (by euclid_assumption "" (show b.sameSide d EF; assumption)))
  euclid_sentence "1.29.17"
    "Thus, (the sum of) $BGH$ and $GHD$ is also equal to two right-angles. "
    (step17 : ∠ b:g:h + ∠ g:h:d = ∟ + ∟) := by euclid_apply (helper_1_29_step17 (by euclid_assumption "" (show ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d; assumption)) (by euclid_assumption "" (show ∠ e:g:b + ∠ b:g:h = ∟ + ∟; assumption)))
  exact ⟨step11, step13, step17⟩
  euclid_conclude_sentence "1.29.18"
    "Thus, a straight-line falling across parallel straight-lines makes the alternate angles equal to one another,  the external (angle) equal to the internal and opposite (angle), and the (sum of the) internal (angles) on the same side equal to two right-angles. (Which is) the very thing it was required to show."

end Elements.Book1
