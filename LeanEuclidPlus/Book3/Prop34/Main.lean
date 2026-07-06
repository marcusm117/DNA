import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_34 : ∀ (ABC : Circle) (d1 d d2 : Point),
  d1 ≠ d ∧ d2 ≠ d →
  ∃ (b c : Point), b.onCircle ABC ∧ c.onCircle ABC ∧ b ≠ c ∧
    ∃ a : Point, a.onCircle ABC ∧ ∠ b:a:c = ∠ d1:d:d2 :=
by
  euclid_intros
  euclid_intro_sentence "3.34.0"
    "To cut off a segment, accepting an angle equal to a given rectilinear angle, from a given circle. Let $ABC$ be the given circle, and $D$ the given rectilinear angle. So it is required to cut off a segment, accepting an angle equal to the given rectilinear angle $D$, from the given circle $ABC$."

  euclid_sentence "3.34.1"
    "Let $EF$ be drawn touching $ABC$ at point $B$.$^\\dag$"
    (step1 : True) := by sorry

  euclid_sentence "3.34.2"
    "And let (angle) $FBC$, equal to angle $D$, be constructed on the straight-line $FB$, at the point $B$ on it [Prop.~1.23]."
    (step2 : True) := by sorry

  -- @assumption ("some straight-line $EF$ touches the circle $ABC$", TODO)
  -- @assumption ("$BC$ has been drawn across (the circle) from the point of contact $B$", TODO)
  euclid_sentence "3.34.3"
    "Therefore, since some straight-line $EF$ touches the circle $ABC$, and $BC$ has been drawn across (the circle) from the point of contact $B$, angle $FBC$ is thus equal to the angle constructed in the alternate segment $BAC$ [Prop.~1.32]."
    (step3 : True) := by sorry

  euclid_sentence "3.34.4"
    "But, $FBC$ is equal to $D$."
    (step4 : True) := by sorry

  euclid_sentence "3.34.5"
    "Thus, the (angle) in the segment $BAC$ is also equal to [angle] $D$."
    (step5 : True) := by sorry

  -- NOTE: existential conclusion — `exact step5` won't close the goal.
  -- The existential witness + betweenness/construction proof needs manual fixup.
  sorry
  euclid_conclude_sentence "3.34.6"
    "Thus, the segment $BAC$, accepting an angle equal to the given rectilinear angle $D$, has been cut off from the given circle $ABC$. (Which is) the very thing it was required to do."

end Elements.Book3
