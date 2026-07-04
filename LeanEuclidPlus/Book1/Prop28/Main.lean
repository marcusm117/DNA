import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
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
  · -- Case 1: EGB = GHD
    -- @assumption_valid
    have step1_assumption1 : ∠ e:g:b = ∠ g:h:d := by assumption
    -- @assumption_gap
    have step1_assumption2 : ∠ e:g:b = ∠ a:g:h := by sorry
    -- @assumption ("$EGB$ is equal to $GHD$", ∠ e:g:b = ∠ g:h:d)
    -- @assumption ("$EGB$ is equal to $AGH$ [Prop.~1.15]", ∠ e:g:b = ∠ a:g:h)
    euclid_sentence "1.28.1"
      "For since (in the first case) $EGB$ is equal to $GHD$, but $EGB$ is equal to $AGH$ [Prop.~1.15], $AGH$ is thus also equal to $GHD$."
      (step1 : ∠ a:g:h = ∠ g:h:d) := by sorry
    euclid_sentence "1.28.2"
      "And they are alternate (angles)."
      (step2 : a.opposingSides d EF) := by sorry
    euclid_sentence "1.28.3"
      "Thus, $AB$ is  parallel to $CD$ [Prop.~1.27].  "
      (step3 : ¬(AB.intersectsLine CD)) := by sorry
    exact step3 (by assumption)
  · -- Case 2: BGH + GHD = 2R
    -- @assumption_valid
    have step4_assumption1 : ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := by assumption
    -- @assumption_gap
    have step4_assumption2 : ∠ a:g:h + ∠ b:g:h = ∟ + ∟ := by sorry
    -- @assumption ("$BGH$ and $GHD$ is equal to two right-angles", ∠ b:g:h + ∠ g:h:d = ∟ + ∟)
    -- @assumption ("$AGH$ and $BGH$ is also equal to two right-angles [Prop.~1.13]", ∠ a:g:h + ∠ b:g:h = ∟ + ∟)
    euclid_sentence "1.28.4"
      "Again, since (in the second case, the sum of) $BGH$ and $GHD$ is equal to two right-angles,  and (the sum of) $AGH$ and $BGH$ is also equal to two right-angles [Prop.~1.13],  (the sum of) $AGH$ and $BGH$ is thus equal to (the sum of) $BGH$ and $GHD$."
      (step4 : ∠ a:g:h + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d) := by sorry
    euclid_sentence "1.28.5"
      "Let $BGH$ have been subtracted from both."
      (step5 : ∠ a:g:h + ∠ b:g:h - ∠ b:g:h = ∠ b:g:h + ∠ g:h:d - ∠ b:g:h) := by sorry
    euclid_sentence "1.28.6"
      "Thus, the remainder $AGH$ is equal to the remainder $GHD$."
      (step6 : ∠ a:g:h = ∠ g:h:d) := by sorry
    euclid_sentence "1.28.7"
      "And they are alternate (angles)."
      (step7 : a.opposingSides d EF) := by sorry
    euclid_sentence "1.28.8"
      "Thus, $AB$ is parallel to $CD$ [Prop.~1.27]. "
      (step8 : ¬(AB.intersectsLine CD)) := by sorry
    exact step8 (by assumption)
  euclid_conclude_sentence "1.28.9"
    "Thus, if a straight-line falling across  two straight-lines makes the external angle equal to the internal and opposite angle on the same side, or (makes) the (sum of the) internal (angles) on the same side equal to two right-angles, then the (two) straight-lines will be parallel (to one another). (Which is) the very thing it was required to show."

end Elements.Book1
