import SystemE
import Book3.Prop10.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_24 : ∀ (a e b f : Point) (AB : Line) (AEB CFD : Circle),
  a.onCircle AEB ∧ e.onCircle AEB ∧ b.onCircle AEB ∧
  a.onCircle CFD ∧ f.onCircle CFD ∧ b.onCircle CFD ∧
  distinctPointsOnLine a b AB ∧
  ¬ e.onLine AB ∧ ¬ f.onLine AB ∧
  e.sameSide f AB ∧
  ∠ a:e:b = ∠ a:f:b →
  AEB = CFD :=
by
  euclid_intros
  euclid_intro_sentence "3.24.0"
    "Similar segments of circles on equal straight-lines are equal to one another. For let $AEB$ and $CFD$ be similar segments of circles on the equal straight-lines $AB$ and $CD$ (respectively). I say that segment $AEB$ is equal to segment $CFD$."

  -- @assumption ("the segment $AEB$ is applied to the segment $CFD$, and point $A$ is placed on (point) $C$, and the straight-line $AB$ on $CD$", a.onCircle AEB ∧ a.onCircle CFD ∧ distinctPointsOnLine a b AB)
  -- @assumption ("$AB$ being equal to $CD$", |(a─b)| = |(a─b)|)
  -- orchestrator-post-superposition: claim is a given sub-conjunction; in the post-superposition signature B=D=b, so "B coincides with D" = b on both circles; the @assumption justifies it (AB=CD), the claim IS the assertion (not the justification)
  euclid_sentence "3.24.1"
    "For if the segment $AEB$ is applied to the segment $CFD$, and point $A$ is placed on (point) $C$, and the straight-line $AB$ on $CD$, (then) point $B$ will also coincide with point $D$, on account of $AB$ being equal to $CD$."
    (step1 : b.onCircle AEB ∧ b.onCircle CFD) := by sorry

  -- @assumption ("$AB$ coincides with $CD$", distinctPointsOnLine a b AB)
  -- orchestrator-pre-reductio: step2 asserts AEB=CFD before the reductio (steps 3-5) proves it; Euclid states the conclusion then proves it by contradiction; in Phase B step2.lean is a container enclosing its own reductio argument; redundancy with step6-8 is RULE-3 permitted
  euclid_sentence "3.24.2"
    "And if $AB$ coincides with $CD$, (then) the segment $AEB$ will also coincide with $CFD$."
    (step2 : AEB = CFD) := by sorry

  have habsurd1 : ¬(AEB ≠ CFD) := by
    intro hsuppose1
    -- @assumption ("the straight-line $AB$ coincides with $CD$", distinctPointsOnLine a b AB)
    -- @assumption ("the segment $AEB$ does not coincide with $CFD$", AEB ≠ CFD)
    euclid_sentence "3.24.3"
      "For if the straight-line $AB$ coincides with $CD$, and the segment $AEB$ does not coincide with $CFD$, (then) it will surely either fall inside it, outside (it),$^\\dag$ or it will miss like $CGD$ (in the figure),"
      (step3 : e.insideCircle CFD ∨ e.outsideCircle CFD ∨ ∃ g : Point, g.onCircle AEB ∧ g.onCircle CFD ∧ g ≠ a ∧ g ≠ b) := by sorry

    euclid_sentence "3.24.4"
      "and a circle (will) cut (another) circle at more than two points."
      (step4 : ∃ (p q r : Point), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        p.onCircle AEB ∧ q.onCircle AEB ∧ r.onCircle AEB ∧
        p.onCircle CFD ∧ q.onCircle CFD ∧ r.onCircle CFD) := by sorry

    euclid_sentence "3.24.5"
      "The very thing is impossible [Prop.~3.10]."
      (step5 : False) := by sorry
    exact step5

  -- @assumption ("the straight-line $AB$ is applied to $CD$", distinctPointsOnLine a b AB)
  -- orchestrator-reductio-close: step6 = habsurd1 type (¬(AEB≠CFD)); step7 = positive form (AEB=CFD) by classical double-negation; step8 = same, citing C.N.4 ("coincide ⟹ equal" is the same in our Circle-equality formulation); redundancy across 6-8 is RULE-3 permitted
  euclid_sentence "3.24.6"
    "Thus, if the straight-line $AB$ is applied to $CD$, the segment $AEB$ cannot not also coincide with $CFD$."
    (step6 : ¬(AEB ≠ CFD)) := by sorry

  euclid_sentence "3.24.7"
    "Thus, it will coincide,"
    (step7 : AEB = CFD) := by sorry

  euclid_sentence "3.24.8"
    "and will be equal to it [C.N.~4]."
    (step8 : AEB = CFD) := by sorry

  exact step8
  euclid_conclude_sentence "3.24.9"
    "Thus, similar segments of circles on equal straight-lines are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book3
