import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_27 : ∀ (a d e f : Point) (AE FD EF : Line),
  distinctPointsOnLine a e AE ∧ distinctPointsOnLine f d FD ∧ distinctPointsOnLine e f EF ∧
  a.opposingSides d EF ∧ (∠ a:e:f = ∠ e:f:d) →
  ¬(AE.intersectsLine FD) := by
  -- `euclid_intros` telescopes through the `¬` too: goal becomes `False`, with `AE.intersectsLine FD`
  -- in context — the reductio hypothesis ("if not parallel, then being produced they meet").
  euclid_intros
  euclid_intro_sentence "1.27.0"
    "If a straight-line falling across two straight-lines makes  the alternate angles equal to one another then the (two) straight-lines will be parallel to one another.  For let the straight-line $EF$, falling across the two straight-lines $AB$ and $CD$, make the alternate angles $AEF$ and $EFD$ equal to one another. I say that $AB$ and $CD$ are parallel. "
  euclid_apply (extend_point AE a e) as b
  euclid_apply (intersection_lines AE FD) as g
  -- @assumption_valid
  have step1_assumption1 : AE.intersectsLine FD := by assumption
  -- @assumption ("For if not", AE.intersectsLine FD)
  euclid_sentence "1.27.1"
    "For if not, being produced, $AB$ and $CD$ will certainly meet together: either in the direction of $B$ and $D$, or (in the direction) of $A$ and $C$ [Def.~1.23]."
    (step1 : g.sameSide b EF ∨ g.opposingSides b EF) := by sorry
  -- Euclid takes the B,D direction first and derives a contradiction with Prop 1.16.
  have hBD : ¬(g.sameSide b EF) := by
    intro hbd
    euclid_sentence "1.27.2"
      "Let them have been produced, and let them meet together in the direction of $B$ and $D$ at  (point) $G$."
      (step2 : g.onLine AE ∧ g.onLine FD ∧ g.sameSide b EF) := by sorry
    euclid_sentence "1.27.3"
      "So, for the triangle $GEF$, the external angle $AEF$ is equal to the interior and opposite (angle) $EFG$."
      (step3 : ∠ a:e:f = ∠ e:f:g) := by sorry
    euclid_sentence "1.27.4"
      "The very thing is impossible [Prop.~1.16]."
      (step4 : False) := by sorry
    exact step4
  euclid_sentence "1.27.5"
    "Thus, being produced, $AB$ and $CD$ will not meet together in the direction of $B$ and $D$."
    (step5 : ¬(g.sameSide b EF)) := by sorry
  euclid_sentence "1.27.6"
    "Similarly,  it can be shown that neither (will they meet together) in (the direction of) $A$ and $C$."
    (step6 : ¬(g.opposingSides b EF)) := by sorry
  -- @assumption_valid
  have step7_assumption1 : ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF) := by euclid_finish
  -- @assumption ("meeting in neither direction", ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF))
  euclid_sentence "1.27.7"
    "But  (straight-lines) meeting in neither direction are parallel [Def.~1.23]."
    (step7 : ¬(AE.intersectsLine FD)) := by sorry
  euclid_sentence "1.27.8"
    "Thus, $AB$ and $CD$ are parallel. "
    (step8 : ¬(AE.intersectsLine FD)) := by sorry
  -- The meeting point G would lie on one side of EF (step1) yet on neither (step5, step6): so the
  -- lines meet in no direction, hence do not intersect — contradicting the reductio hypothesis.
  exact step8 (by assumption)
  euclid_conclude_sentence "1.27.9"
    "Thus, if a straight-line falling across two straight-lines makes  the alternate angles equal to one another then the (two) straight-lines will be parallel (to one another). (Which is) the very thing it was required to show."

end Elements.Book1
