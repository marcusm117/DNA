import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_36 : ∀ (a b c d e f g h : Point) (AH BG AB CD EF HG : Line),
  formParallelogram a d b c AH BG AB CD ∧ formParallelogram e h f g AH BG EF HG ∧
  |(b─c)| = |(f─g)| ∧ (between a d h) ∧ (between a e h) →
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g := by
  euclid_intros
  euclid_intro_sentence "1.36.0"
    "Parallelograms which are on equal bases and between the same parallels are equal to one another. Let $ABCD$ and $EFGH$ be parallelograms which are on the equal bases $BC$ and $FG$, and (are) between the same parallels $AH$ and $BG$. I say that the parallelogram $ABCD$ is equal to $EFGH$. "

  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c h) as CH
  euclid_sentence "1.36.1"
    "For let $BE$ and $CH$ have been joined."
    (step1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH) := by sorry

  -- @assumption_valid
  have step2_assumption1 : |(b─c)| = |(f─g)| := by assumption
  -- @assumption_gap
  have step2_assumption2 : |(f─g)| = |(e─h)| := by sorry
  -- @assumption ("$BC$ is equal to $FG$", |(b─c)| = |(f─g)|)
  -- @assumption ("$FG$ is equal to $EH$ [Prop.~1.34]", |(f─g)| = |(e─h)|)
  euclid_sentence "1.36.2"
    "And since $BC$ is equal to $FG$, but $FG$ is equal to $EH$ [Prop.~1.34], $BC$ is thus equal to $EH$."
    (step2 : |(b─c)| = |(e─h)|) := by sorry

  euclid_sentence "1.36.3"
    "And they are also parallel,"
    (step3 : ¬(BG.intersectsLine AH)) := by sorry

  euclid_sentence "1.36.4"
    "and $EB$ and $HC$ join them."
    (step4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH) := by sorry

  euclid_sentence "1.36.5"
    "But (straight-lines) joining equal and parallel (straight-lines) on the same sides are (themselves) equal and parallel [Prop.~1.33] [thus, $EB$ and $HC$ are also equal and parallel]."
    (step5 : |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH)) := by sorry

  euclid_sentence "1.36.6"
    "Thus, $EBCH$ is a parallelogram [Prop.~1.34],"
    (step6 : formParallelogram e h b c AH BG BE CH) := by sorry

  -- @assumption_valid
  have step7_assumption1 : distinctPointsOnLine b c BG := by euclid_finish
  -- @assumption_valid
  have step7_assumption2 : ¬(BG.intersectsLine AH) := by assumption
  -- @assumption ("$BC$, as ($ABCD$)", distinctPointsOnLine b c BG)
  -- @assumption ("$BC$ and $AH$, as ($ABCD$) [Prop.~1.35]", ¬(BG.intersectsLine AH))
  euclid_sentence "1.36.7"
    "and is equal to $ABCD$. For it has  the same base, $BC$, as ($ABCD$), and is between the same parallels, $BC$ and $AH$, as ($ABCD$) [Prop.~1.35]."
    (step7 : Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c) := by sorry

  euclid_sentence "1.36.8"
    "So, for the same (reasons), $EFGH$ is also equal to the same (parallelogram) $EBCH$ [Prop.~1.34]. "
    (step8 : Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h) := by sorry

  euclid_sentence "1.36.9"
    "So that the parallelogram $ABCD$ is  also equal to $EFGH$. "
    (step9 : Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g) := by sorry

  exact step9
  euclid_conclude_sentence "1.36.10"
    "Thus, parallelograms which are on equal bases and between the same parallels are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
