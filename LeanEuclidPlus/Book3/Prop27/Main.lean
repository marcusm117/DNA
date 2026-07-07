import SystemE
import Book3.Prop20.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_27 : ∀ (a b c d e f g h : Point) (BC EF : Line) (ABC DEF : Circle),
  g.isCentre ABC ∧ h.isCentre DEF ∧
  b.onCircle ABC ∧ c.onCircle ABC ∧ e.onCircle DEF ∧ f.onCircle DEF ∧
  a.onCircle ABC ∧ d.onCircle DEF ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧
  a ≠ b ∧ a ≠ c ∧ d ≠ e ∧ d ≠ f ∧
  a.sameSide g BC ∧ d.sameSide h EF ∧
  |(g─b)| = |(h─e)| ∧
  ∠ b:g:c = ∠ e:h:f →
  ∠ b:a:c = ∠ e:d:f :=
by
  euclid_intros
  euclid_intro_sentence "3.27.0"
    "In equal circles, angles standing upon equal circumferences are equal to one another, whether they are standing at the center or at the circumference. For let the angles $BGC$ and $EHF$ at the centers $G$ and $H$, and the (angles) $BAC$ and $EDF$ at the circumferences, stand upon the equal circumferences $BC$ and $EF$, in the equal circles $ABC$ and $DEF$ (respectively). I say that angle $BGC$ is equal to (angle) $EHF$, and $BAC$ is equal to $EDF$."

  have habsurd1 : ¬(∠ b:g:c ≠ ∠ e:h:f) := by
    intro hsuppose1
    -- @assumption ("$BGC$ is unequal to $EHF$", ∠ b:g:c ≠ ∠ e:h:f)
    euclid_sentence "3.27.1"
      "For if $BGC$ is unequal to $EHF$, one of them is greater."
      (step1 : ∠ b:g:c > ∠ e:h:f ∨ ∠ e:h:f > ∠ b:g:c) := by sorry

    euclid_sentence "3.27.2"
      "Let $BGC$ be greater,"
      (step2 : ∠ b:g:c > ∠ e:h:f) := by sorry

    -- Introduce K by [Prop.~1.23]: construct angle BGK = EHF at G on line BG
    have hK_ex : ∃ k : Point, k ≠ g ∧ ∠ b:g:k = ∠ e:h:f := by sorry
    obtain ⟨k, hk_ne_g, hk_angle⟩ := hK_ex
    euclid_sentence "3.27.3"
      "and let the (angle) $BGK$, equal to angle $EHF$, be constructed on the straight-line $BG$, at the point $G$ on it [Prop.~1.23]."
      (step3 : ∠ b:g:k = ∠ e:h:f) := by sorry

    -- @assumption ("equal angles (in equal circles) stand upon equal circumferences, when they are at the centers", ∠ b:g:k = ∠ e:h:f)
    euclid_sentence "3.27.4"
      "But equal angles (in equal circles) stand upon equal circumferences, when they are at the centers [Prop.~3.26]. Thus, circumference $BK$ (is) equal to circumference $EF$."
      (step4 : ∠ b:g:k = ∠ e:h:f) := by sorry

    euclid_sentence "3.27.5"
      "But, $EF$ is equal to $BC$."
      (step5 : ∠ e:h:f = ∠ b:g:c) := by sorry

    euclid_sentence "3.27.6"
      "Thus, $BK$ is also equal to $BC$, the lesser to the greater."
      (step6 : ∠ b:g:k = ∠ b:g:c) := by sorry

    euclid_sentence "3.27.7"
      "The very thing is impossible."
      (step7 : False) := by sorry
    exact step7

  euclid_sentence "3.27.8"
    "Thus, angle $BGC$ is not unequal to $EHF$."
    (step8 : ¬(∠ b:g:c ≠ ∠ e:h:f)) := by sorry

  euclid_sentence "3.27.9"
    "Thus, (it is) equal."
    (step9 : ∠ b:g:c = ∠ e:h:f) := by sorry

  euclid_sentence "3.27.10"
    "And the (angle) at $A$ is half $BGC$,"
    (step10 : ∠ b:g:c = ∠ b:a:c + ∠ b:a:c) := by sorry

  -- @assumption deferred: [Prop.~3.20] gives central = double inscribed
  euclid_sentence "3.27.11"
    "and the (angle) at $D$ half $EHF$ [Prop.~3.20]."
    (step11 : ∠ e:h:f = ∠ e:d:f + ∠ e:d:f) := by sorry

  euclid_sentence "3.27.12"
    "Thus, the angle at $A$ (is) also equal to the (angle) at $D$."
    (step12 : ∠ b:a:c = ∠ e:d:f) := by sorry

  exact step12
  euclid_conclude_sentence "3.27.13"
    "Thus, in equal circles, angles standing upon equal circumferences are equal to one another, whether they are standing at the center or at the circumference. (Which is) the very thing it was required to show."

end Elements.Book3
