import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_4 : ∀ (a b c d e f : Point) (AC BD : Line) (ABCD : Circle),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  f.isCentre ABCD ∧ ¬f.onLine AC ∧ ¬f.onLine BD ∧
  between a e c ∧ between b e d →
  ¬(|(a─e)| = |(e─c)| ∧ |(b─e)| = |(e─d)|) :=
by
  euclid_intros
  euclid_intro_sentence "3.4.0"
    "In a circle, if two straight-lines, which are not through the center, cut one another, (then) they do not cut one another in half. Let $ABCD$ be a circle, and within it, let two straight-lines, $AC$ and $BD$, which are not through the center, cut one another at (point) $E$. I say that they do not cut one another in half."

  euclid_sentence "3.4.1"
    "For, if possible, let them cut one another in half, such that $AE$ is equal to $EC$,"
    (step1 : |(a─e)| = |(e─c)|) := by sorry

  euclid_sentence "3.4.2"
    "and $BE$ to $ED$."
    (step2 : |(b─e)| = |(e─d)|) := by sorry

  -- orchestrator-note: f.isCentre ABCD coincides with the outer hypothesis; faithful since the sentence asserts "let F be the center" and f is already baked into the signature by the signature phase. No euclid_apply (proposition_1 ...) needed — f is a ∀-binder in the signature.
  euclid_sentence "3.4.3"
    "And let the center of the circle $ABCD$ be found [Prop.~3.1], and let it be (at point) $F$,"
    (step3 : f.isCentre ABCD) := by sorry

  euclid_apply (line_from_points f e) as FE
  euclid_sentence "3.4.4"
    "and let $FE$ be joined."
    (step4 : distinctPointsOnLine f e FE) := by sorry

  -- @assumption ("some straight-line through the center, $FE$, cuts in half some straight-line not through the center, $AC$", |(a─e)| = |(e─c)|)
  euclid_sentence "3.4.5"
    "Therefore, since some straight-line through the center, $FE$, cuts in half some straight-line not through the center, $AC$, it also cuts it at right-angles [Prop.~3.3]."
    (step5 : ∠ f:e:a = ∟) := by sorry

  -- orchestrator-note: redundant with step5 (RULE 3 permitted); Euclid names the specific angle FEA explicitly.
  euclid_sentence "3.4.6"
    "Thus, $FEA$ is a right-angle."
    (step6 : ∠ f:e:a = ∟) := by sorry

  -- @assumption ("some straight-line $FE$ cuts in half some straight-line $BD$", |(b─e)| = |(e─d)|)
  euclid_sentence "3.4.7"
    "Again, since some straight-line $FE$ cuts in half some straight-line $BD$, it also cuts it at right-angles [Prop.~3.3]."
    (step7 : ∠ f:e:b = ∟) := by sorry

  -- orchestrator-note: redundant with step7 (RULE 3 permitted); Euclid names the specific angle FEB explicitly.
  euclid_sentence "3.4.8"
    "Thus, $FEB$ (is) a right-angle."
    (step8 : ∠ f:e:b = ∟) := by sorry

  -- @assumption ("But $FEA$ was also shown (to be) a right-angle", ∠ f:e:a = ∟)
  euclid_sentence "3.4.9"
    "But $FEA$ was also shown (to be) a right-angle. Thus, $FEA$ (is) equal to $FEB$, the lesser to the greater."
    (step9 : ∠ f:e:a = ∠ f:e:b) := by sorry

  euclid_sentence "3.4.10"
    "The very thing is impossible."
    (step10 : False) := by sorry

  exact step10
  euclid_conclude_sentence "3.4.11"
    "Thus, $AC$ and $BD$ do not cut one another in half."
  euclid_conclude_sentence "3.4.12"
    "Thus, in a circle, if two straight-lines, which are not through the center, cut one another, (then) they do not cut one another in half. (Which is) the very thing it was required to show."

end Elements.Book3
