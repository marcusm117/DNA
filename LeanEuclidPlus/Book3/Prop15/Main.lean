import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_15 : ∀ (a b c d e f g h k : Point) (ABCD : Circle) (BC FG : Line),
  e.isCentre ABCD ∧
  a.onCircle ABCD ∧ d.onCircle ABCD ∧ between a e d ∧
  b.onCircle ABCD ∧ c.onCircle ABCD ∧ distinctPointsOnLine b c BC ∧
  f.onCircle ABCD ∧ g.onCircle ABCD ∧ distinctPointsOnLine f g FG ∧
  h.onLine BC ∧ ∠ e:h:b = ∟ ∧
  k.onLine FG ∧ ∠ e:k:f = ∟ ∧
  |(e─h)| < |(e─k)| →
  |(a─d)| > |(b─c)| ∧ |(b─c)| > |(f─g)| :=
by
  euclid_intros
  euclid_intro_sentence "3.15.0"
    "In a circle, a diameter (is) the greatest (straight-line), and for the others, a (straight-line) nearer to the center is always greater than one further away. Let $ABCD$ be a circle, and let $AD$ be its diameter, and $E$ (its) center. And let $BC$ be nearer to the diameter $AD$,$^\\dag$ and $FG$ further away. I say that $AD$ is the greatest (straight-line), and $BC$ (is) greater than $FG$."

  -- Introduce line objects EH and EK via have (avoiding e ≠ h/k side conditions)
  have hlines : ∃ EH EK : Line, distinctPointsOnLine e h EH ∧ distinctPointsOnLine e k EK := by sorry
  obtain ⟨EH, EK, hEH, hEK⟩ := hlines
  euclid_sentence "3.15.1"
    "For let $EH$ and $EK$ be drawn from the center $E$, at right-angles to $BC$ and $FG$ (respectively) [Prop.~1.12]."
    (step1 : distinctPointsOnLine e h EH ∧ distinctPointsOnLine e k EK) := by sorry

  -- @assumption ("$BC$ is nearer to the center, and $FG$ further away", |(e─h)| < |(e─k)|)
  euclid_sentence "3.15.2"
    "And since $BC$ is nearer to the center, and $FG$ further away, $EK$ (is) thus greater than $EH$ [Def.~3.5]."
    (step2 : |(e─k)| > |(e─h)|) := by sorry

  -- Introduce point L on EK with |EL| = |EH| via have (avoids proposition_3 line-arg issues)
  have hstep3 : ∃ l : Point, between e l k ∧ |(e─l)| = |(e─h)| := by sorry
  obtain ⟨l, hl_betw, hl_eq⟩ := hstep3
  euclid_sentence "3.15.3"
    "Let $EL$ be made equal to $EH$ [Prop.~1.3]."
    (step3 : |(e─l)| = |(e─h)|) := by sorry

  -- Introduce: m0 (off EK perpendicular at l), MN line, circle-intersection points m and n
  have hstep4_aux : ∃ (m0 : Point) (MN : Line),
      ¬(m0.onLine EK) ∧ ∠ e:l:m0 = ∟ ∧ distinctPointsOnLine l m0 MN := by sorry
  obtain ⟨m0, MN, hm0_off, hm0_perp, hMN⟩ := hstep4_aux
  have hstep4_pts : ∃ m n : Point,
      m.onCircle ABCD ∧ n.onCircle ABCD ∧ between m l n ∧ ∠ m:l:e = ∟ ∧
      m.onLine MN ∧ n.onLine MN := by sorry
  obtain ⟨m, n, hm_on, hn_on, hbetw, hperp, hm_MN, hn_MN⟩ := hstep4_pts
  euclid_sentence "3.15.4"
    "And $LM$ being drawn through $L$, at right-angles to $EK$ [Prop.~1.11], let it be drawn through to $N$."
    (step4 : m.onCircle ABCD ∧ n.onCircle ABCD ∧ between m l n ∧ ∠ m:l:e = ∟) := by sorry

  euclid_apply (line_from_points m e) as ME
  euclid_apply (line_from_points e n) as EN
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points e g) as EG
  euclid_sentence "3.15.5"
    "And let $ME$, $EN$, $FE$, and $EG$ be joined."
    (step5 : distinctPointsOnLine m e ME ∧ distinctPointsOnLine e n EN ∧ distinctPointsOnLine f e FE ∧ distinctPointsOnLine e g EG) := by sorry

  -- @assumption ("$EH$ is equal to $EL$", |(e─h)| = |(e─l)|)
  euclid_sentence "3.15.6"
    "And since $EH$ is equal to $EL$, $BC$ is also equal to $MN$ [Prop.~3.14]."
    (step6 : |(b─c)| = |(m─n)|) := by sorry

  -- @assumption ("$AE$ is equal to $EM$, and $ED$ to $EN$", |(a─e)| = |(m─e)| ∧ |(e─d)| = |(e─n)|)
  euclid_sentence "3.15.7"
    "Again, since $AE$ is equal to $EM$, and $ED$ to $EN$, $AD$ is thus equal to $ME$ and $EN$."
    (step7 : |(a─d)| = |(m─e)| + |(e─n)|) := by sorry

  euclid_sentence "3.15.8"
    "But, $ME$ and $EN$ is greater than $MN$ [Prop.~1.20] [also $AD$ is greater than $MN$],"
    (step8 : |(m─e)| + |(e─n)| > |(m─n)|) := by sorry

  euclid_sentence "3.15.9"
    "and $MN$ (is) equal to $BC$."
    (step9 : |(m─n)| = |(b─c)|) := by sorry

  euclid_sentence "3.15.10"
    "Thus, $AD$ is greater than $BC$."
    (step10 : |(a─d)| > |(b─c)|) := by sorry

  -- @assumption ("the two (straight-lines) $ME$, $EN$ are equal to the two (straight-lines) $FE$, $EG$ (respectively)", |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)|)
  -- @assumption ("angle $MEN$ [is] greater than angle $FEG$", ∠ m:e:n > ∠ f:e:g)
  euclid_sentence "3.15.11"
    "And since the two (straight-lines) $ME$, $EN$ are equal to the two (straight-lines) $FE$, $EG$ (respectively), and angle $MEN$ [is] greater than angle $FEG$,$^\\ddag$ the base $MN$ is thus greater than the base $FG$ [Prop.~1.24]."
    (step11 : |(m─n)| > |(f─g)|) := by sorry

  -- @assumption ("$MN$ was shown (to be) equal to $BC$", |(m─n)| = |(b─c)|)
  euclid_sentence "3.15.12"
    "But, $MN$ was shown (to be) equal to $BC$ [(so) $BC$ is also greater than $FG$]."
    (step12 : |(b─c)| > |(f─g)|) := by sorry

  euclid_sentence "3.15.13"
    "Thus, the diameter $AD$ (is) the greatest (straight-line),"
    (step13 : |(a─d)| > |(b─c)|) := by sorry

  euclid_sentence "3.15.14"
    "and $BC$ (is) greater than $FG$."
    (step14 : |(b─c)| > |(f─g)|) := by sorry

  exact ⟨step13, step14⟩
  euclid_conclude_sentence "3.15.15"
    "Thus, in a circle, a diameter (is) the greatest (straight-line), and for the others, a (straight-line) nearer to the center is always greater than one further away. (Which is) the very thing it was required to show."

end Elements.Book3
