import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_30 : ∀ (AB CD EF : Line),
  AB ≠ CD ∧ CD ≠ EF ∧ EF ≠ AB ∧ ¬(AB.intersectsLine EF) ∧ ¬(CD.intersectsLine EF) →
  ¬(AB.intersectsLine CD) := by
  euclid_intros
  euclid_intro_sentence "1.30.0"
    "(Straight-lines) parallel to the same straight-line are also parallel to one another.  Let each of the (straight-lines) $AB$ and $CD$ be parallel to $EF$. I say that $AB$ is also parallel to $CD$. "

  euclid_apply (line_nonempty AB) as g
  euclid_apply (exists_distincts_points_on_line CD g) as k
  euclid_apply (line_from_points g k) as GK
  euclid_apply (intersection_lines EF GK) as h
  euclid_apply (exists_distincts_points_on_line AB g) as a
  euclid_apply (extend_point AB a g) as b
  euclid_apply (point_on_line_same_side GK EF a) as e
  euclid_apply (extend_point EF e h) as f
  euclid_apply (point_on_line_same_side GK CD a) as c
  euclid_apply (extend_point CD c k) as d

  euclid_sentence "1.30.1"
    "For let the straight-line $GK$ fall across  ($AB$, $CD$, and $EF$). "
    (step1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK) := by sorry

  -- @assumption_valid
  have step2_assumption1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF) := by euclid_finish
  -- @assumption ("the straight-line $GK$ has fallen across the parallel straight-lines $AB$ and $EF$", AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))
  euclid_sentence "1.30.2"
    "And since the straight-line $GK$ has fallen across the parallel straight-lines $AB$ and $EF$, (angle) $AGK$ (is) thus equal to $GHF$ [Prop.~1.29]."
    (step2 : ∠ a:g:k = ∠ g:h:f) := by sorry

  -- @assumption_valid
  have step3_assumption1 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF) := by euclid_finish
  -- @assumption ("the straight-line $GK$ has fallen across the parallel straight-lines $EF$ and $CD$", EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF))
  euclid_sentence "1.30.3"
    "Again, since the straight-line $GK$ has fallen across the parallel straight-lines $EF$ and $CD$, (angle) $GHF$ is equal to $GKD$ [Prop.~1.29]."
    (step3 : ∠ g:h:f = ∠ g:k:d) := by sorry

  euclid_sentence "1.30.4"
    "But $AGK$ was also shown (to be) equal to $GHF$."
    (step4 : ∠ a:g:k = ∠ g:h:f) := by sorry

  euclid_sentence "1.30.5"
    "Thus, $AGK$ is also equal to  $GKD$."
    (step5 : ∠ a:g:k = ∠ g:k:d) := by sorry

  euclid_sentence "1.30.6"
    "And they are alternate (angles)."
    (step6 : a.opposingSides d GK) := by sorry

  euclid_sentence "1.30.7"
    "Thus, $AB$ is parallel to $CD$ [Prop.~1.27]."
    (step7 : ¬(AB.intersectsLine CD)) := by sorry

  exact step7 (by assumption)
  euclid_conclude_sentence "1.30.8"
    "Thus, (straight-lines) parallel to the same straight-line are also parallel to one another.] (Which is) the very thing it was required to show."

end Elements.Book1
