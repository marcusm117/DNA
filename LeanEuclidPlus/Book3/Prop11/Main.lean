import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_11 : ∀ (a f g : Point) (ABC ADE : Circle),
  a.onCircle ABC ∧ a.onCircle ADE ∧
  ¬ ABC.intersectsCircle ADE ∧
  g.insideCircle ABC ∧
  f.isCentre ABC ∧ g.isCentre ADE ∧
  f ≠ g →
  between f g a :=
by
  euclid_intros
  euclid_intro_sentence "3.11.0"
    "If two circles touch one another internally, and their centers are found, (then) the straight-line joining their centers, being produced, will fall upon the point of union of the circles. For let two circles, $ABC$ and $ADE$, touch one another internally at point $A$, and let the center $F$ of circle $ABC$ be found [Prop.~3.1], and (the center) $G$ of (circle) $ADE$ [Prop.~3.1]. I say that the straight-line joining $G$ to $F$, being produced, will fall on $A$."

  have habsurd1 : ¬(¬(between f g a)) := by
    intro hsuppose1
    euclid_sentence "3.11.1"
      "For (if) not (then), if possible, let it fall like $FGH$ (in the figure),"
      (step1 : ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h) := by sorry
    obtain ⟨h, h_ne, h_on_ABC, h_bet_fgh⟩ := step1
    -- D is the point where line FGH exits circle ADE (between G and H on the line)
    have hd_ex : ∃ d : Point, d.onCircle ADE ∧ between g d h := by sorry
    obtain ⟨d, hd_on_ADE, hd_bet_gdh⟩ := hd_ex
    euclid_apply (line_from_points a f) as AF
    euclid_apply (line_from_points a g) as AG
    euclid_sentence "3.11.2"
      "and let $AF$ and $AG$ be joined."
      (step2 : distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG) := by sorry
    -- @assumption ("that is to say $FH$", |(f─a)| = |(f─h)|)
    -- @assumption ("since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]", |(a─g)| + |(g─f)| > |(f─h)|)
    euclid_sentence "3.11.3"
      "Therefore, since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20], let $FG$ be taken from both."
      (step3 : |(a─g)| > |(f─h)| - |(g─f)|) := by sorry
    euclid_sentence "3.11.4"
      "Thus, the remainder $AG$ is greater than the remainder $GH$."
      (step4 : |(a─g)| > |(g─h)|) := by sorry
    euclid_sentence "3.11.5"
      "And $AG$ (is) equal to $GD$."
      (step5 : |(a─g)| = |(g─d)|) := by sorry
    euclid_sentence "3.11.6"
      "Thus, $GD$ is also greater than $GH$, the lesser than the greater."
      (step6 : |(g─d)| > |(g─h)|) := by sorry
    euclid_sentence "3.11.7"
      "The very thing is impossible."
      (step7 : False) := by sorry
    exact step7

  euclid_sentence "3.11.8"
    "Thus, the straight-line joining $F$ to $G$ will not fall outside (one circle but inside the other)."
    (step8 : ¬(¬(between f g a))) := by sorry

  euclid_sentence "3.11.9"
    "Thus, it will fall upon the point of union (of the circles) at point $A$."
    (step9 : between f g a) := by sorry

  exact step9
  euclid_conclude_sentence "3.11.10"
    "Thus, if two circles touch one another internally, [and their centers are found], (then) the straight-line joining their centers, [being produced], will fall upon the point of union of the circles. (Which is) the very thing it was required to show."

end Elements.Book3
