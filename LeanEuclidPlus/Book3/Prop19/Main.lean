import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_19 : ∀ (a c e : Point) (ABC : Circle) (DE CA : Line),
  c.onLine DE ∧ c.onCircle ABC ∧ ¬ DE.intersectsCircle ABC ∧
  a.onLine CA ∧ c.onLine CA ∧ a ≠ c ∧
  e.onLine DE ∧ e ≠ c ∧ ∠ a:c:e = ∟ →
  ∀ o : Point, o.isCentre ABC → o.onLine CA :=
by
  euclid_intros
  euclid_intro_sentence "3.19.0"
    "If some straight-line touches a circle, and a straight-line is drawn from the point of contact, at right-[angles] to the tangent, (then) the center (of the circle) will be on the (straight-line) so drawn. For let some straight-line $DE$ touch the circle $ABC$ at point $C$. And let $CA$ be drawn from $C$, at right-angles to $DE$ [Prop.~1.11]. I say that the center of the circle is on $AC$."

  have habsurd1 : ¬(¬o.onLine CA) := by
    intro hsuppose1
    -- orchestrator-note: step1 restates given o.isCentre ABC; faithful to "let F be the center"
    -- (F=o in the formal proof; the sentence names the reductio's hypothetical center).
    euclid_sentence "3.19.1"
      "For (if) not, if possible, let $F$ be (the center of the circle),"
      (step1 : o.isCentre ABC) := by sorry

    euclid_apply (line_from_points o c) as CF
    euclid_sentence "3.19.2"
      "and let $CF$ be joined."
      (step2 : o.onLine CF ∧ c.onLine CF) := by sorry

    -- @assumption ("some straight-line $DE$ touches the circle $ABC$", c.onCircle ABC ∧ c.onLine DE ∧ ¬DE.intersectsCircle ABC)
    -- @assumption ("$FC$ has been joined from the center to the point of contact", o.isCentre ABC ∧ o ≠ c)
    euclid_sentence "3.19.3"
      "[Therefore], since some straight-line $DE$ touches the circle $ABC$, and $FC$ has been joined from the center to the point of contact, $FC$ is thus perpendicular to $DE$ [Prop.~3.18]."
      (step3 : ∠ o:c:e = ∟) := by sorry

    euclid_sentence "3.19.4"
      "Thus, $FCE$ is a right-angle."
      (step4 : ∠ o:c:e = ∟) := by sorry

    -- orchestrator-note: step5 restates given ∠a:c:e = ∟; Euclid quotes the given for the
    -- comparison with step4/step3 that yields the contradiction.
    euclid_sentence "3.19.5"
      "And $ACE$ is also a right-angle."
      (step5 : ∠ a:c:e = ∟) := by sorry

    euclid_sentence "3.19.6"
      "Thus, $FCE$ is equal to $ACE$, the lesser to the greater."
      (step6 : ∠ o:c:e = ∠ a:c:e) := by sorry

    euclid_sentence "3.19.7"
      "The very thing is impossible."
      (step7 : False) := by sorry
    exact step7

  -- orchestrator-note: step8 "F is not the center" = reductio_close; formally ¬(¬o.onLine CA)
  -- (the center cannot be a point off CA; F [= supposed center off CA] is not the center).
  euclid_sentence "3.19.8"
    "Thus, $F$ is not the center of circle $ABC$."
    (step8 : ¬(¬o.onLine CA)) := by sorry

  euclid_sentence "3.19.9"
    "So, similarly, we can show that neither is any (point) other (than one) on $AC$."
    (step9 : o.onLine CA) := by sorry

  exact step9
  euclid_conclude_sentence "3.19.10"
    "Thus, if some straight-line touches a circle, and a straight-line is drawn from the point of contact, at right-angles to the tangent, (then) the center (of the circle) will be on the (straight-line) so drawn. (Which is) the very thing it was required to show."

end Elements.Book3
