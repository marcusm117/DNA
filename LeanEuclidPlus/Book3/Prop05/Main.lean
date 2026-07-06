import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_5 : ∀ (ABC CDG : Circle),
  ABC.intersectsCircle CDG →
  ¬ ∃ e : Point, e.isCentre ABC ∧ e.isCentre CDG :=
by
  euclid_intros
  euclid_intro_sentence "3.5.0"
    "If two circles cut one another, (then) they will not have the same center. For let the two circles $ABC$ and $CDG$ cut one another at points $B$ and $C$. I say that they will not have the same center."

  -- euclid_intros intro'd through ¬; goal is False;
  -- ∃ e, e.isCentre ABC ∧ e.isCentre CDG is in context.
  obtain ⟨e, hecABC, hecdg⟩ := ‹∃ e : Point, e.isCentre ABC ∧ e.isCentre CDG›
  -- Get C, a point lying on both circles.
  euclid_apply (intersection_circles ABC CDG) as c
  -- Construct line EC through e and c (e ≠ c: center is inside, c is on, circle).
  have hEC_exists : ∃ EC : Line, e.onLine EC ∧ c.onLine EC := by sorry
  obtain ⟨EC, hEC_e, hEC_c⟩ := hEC_exists
  -- Construct EFG: a random line through e hitting ABC at f and CDG at g, with f between e and g.
  have hEFG_exists : ∃ (EFG : Line) (f g : Point),
      e.onLine EFG ∧ f.onCircle ABC ∧ f.onLine EFG ∧
      g.onCircle CDG ∧ g.onLine EFG ∧ between e f g := by sorry
  obtain ⟨EFG, f, g, hEFG_e, hf_ABC, hf_EFG, hg_CDG, hg_EFG, hbetween⟩ := hEFG_exists

  euclid_sentence "3.5.1"
    "For, if possible, let $E$ be (the common center),"
    (step1 : e.isCentre ABC ∧ e.isCentre CDG) := by sorry

  euclid_sentence "3.5.2"
    "and let $EC$ be joined,"
    (step2 : e.onLine EC ∧ c.onLine EC) := by sorry

  euclid_sentence "3.5.3"
    "and let $EFG$ be drawn through (the two circles), at random."
    (step3 : e.onLine EFG ∧ f.onCircle ABC ∧ f.onLine EFG ∧
             g.onCircle CDG ∧ g.onLine EFG ∧ between e f g) := by sorry

  -- @assumption ("point $E$ is the center of the circle $ABC$", e.isCentre ABC)
  euclid_sentence "3.5.4"
    "And since point $E$ is the center of the circle $ABC$, $EC$ is equal to $EF$."
    (step4 : |(e─c)| = |(e─f)|) := by sorry

  -- @assumption ("point $E$ is the center of the circle $CDG$", e.isCentre CDG)
  euclid_sentence "3.5.5"
    "Again, since point $E$ is the center of the circle $CDG$, $EC$ is equal to $EG$."
    (step5 : |(e─c)| = |(e─g)|) := by sorry

  euclid_sentence "3.5.6"
    "But $EC$ was also shown (to be) equal to $EF$."
    (step6 : |(e─c)| = |(e─f)|) := by sorry

  euclid_sentence "3.5.7"
    "Thus, $EF$ is also equal to $EG$, the lesser to the greater."
    (step7 : |(e─f)| = |(e─g)|) := by sorry

  euclid_sentence "3.5.8"
    "The very thing is impossible."
    (step8 : False) := by sorry

  euclid_sentence "3.5.9"
    "Thus, point $E$ is not the (common) center of the circles $ABC$ and $CDG$."
    (step9 : ¬(e.isCentre ABC ∧ e.isCentre CDG)) := by sorry

  exact step8
  euclid_conclude_sentence "3.5.10"
    "Thus, if two circles cut one another, (then) they will not have the same center. (Which is) the very thing it was required to show."

end Elements.Book3
