import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_6 : ∀ (ABC CDE : Circle),
  (∃ p : Point, p.onCircle ABC ∧ p.onCircle CDE) ∧ ¬ ABC.intersectsCircle CDE →
  ¬ ∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE :=
by
  euclid_intros
  -- euclid_intros telescopes through ¬: splits the conjunction into `left`/`right`,
  -- introduces the negation's argument as `a✝ : ∃ f, f.isCentre ABC ∧ f.isCentre CDE`,
  -- leaving goal : False.
  euclid_intro_sentence "3.6.0"
    "If two circles touch one another, (then) they will not have the same center. For let the two circles $ABC$ and $CDE$ touch one another at point $C$. I say that they will not have the same center."
  -- Unpack the touch point c from `left : ∃ p, p.onCircle ABC ∧ p.onCircle CDE`
  obtain ⟨c, hcABC, hcCDE⟩ := left

  have habsurd1 : ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE) := by
    intro hsuppose1
    obtain ⟨f, hfABC, hfCDE⟩ := hsuppose1
    euclid_sentence "3.6.1"
      "For, if possible, let $F$ be (the common center),"
      (step1 : f.isCentre ABC ∧ f.isCentre CDE) := by sorry

    euclid_apply (line_from_points f c) as FC
    euclid_sentence "3.6.2"
      "and let $FC$ be joined,"
      (step2 : f.onLine FC ∧ c.onLine FC) := by sorry

    -- Introduce line FEB with b on circle ABC, e on circle CDE, E between F and B
    have hFEB : ∃ (b e : Point) (FEB : Line),
        b.onCircle ABC ∧ e.onCircle CDE ∧ between f e b ∧
        f.onLine FEB ∧ e.onLine FEB ∧ b.onLine FEB := by sorry
    obtain ⟨b, e, FEB, hbABC, heCDE, hbetw, hfFEB, heFEB, hbFEB⟩ := hFEB
    euclid_sentence "3.6.3"
      "and let $FEB$ be drawn through (the two circles), at random."
      (step3 : b.onCircle ABC ∧ e.onCircle CDE ∧ between f e b ∧
               f.onLine FEB ∧ e.onLine FEB ∧ b.onLine FEB) := by sorry

    -- @assumption ("point $F$ is the center of the circle $ABC$", f.isCentre ABC)
    euclid_sentence "3.6.4"
      "Therefore, since point $F$ is the center of the circle $ABC$, $FC$ is equal to $FB$."
      (step4 : |(f─c)| = |(f─b)|) := by sorry

    -- @assumption ("point $F$ is the center of the circle $CDE$", f.isCentre CDE)
    euclid_sentence "3.6.5"
      "Again, since point $F$ is the center of the circle $CDE$, $FC$ is equal to $FE$."
      (step5 : |(f─c)| = |(f─e)|) := by sorry

    -- @assumption ("$FC$ was shown (to be) equal to $FB$", |(f─c)| = |(f─b)|)
    euclid_sentence "3.6.6"
      "But $FC$ was shown (to be) equal to $FB$. Thus, $FE$ is also equal to $FB$, the lesser to the greater."
      (step6 : |(f─e)| = |(f─b)|) := by sorry

    euclid_sentence "3.6.7"
      "The very thing is impossible."
      (step7 : False) := by sorry
    exact step7

  euclid_sentence "3.6.8"
    "Thus, point $F$ is not the (common) center of the circles $ABC$ and $CDE$."
    (step8 : ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE)) := by sorry
  -- step8 : ¬∃f,... applied to the telescoped reductio hyp (a✝) closes the False goal
  exact step8 ‹∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE›
  euclid_conclude_sentence "3.6.9"
    "Thus, if two circles touch one another, (then) they will not have the same center. (Which is) the very thing it was required to show."

end Elements.Book3
