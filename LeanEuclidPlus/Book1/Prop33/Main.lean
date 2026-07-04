import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_33 : ∀ (a b c d : Point) (AB CD AC BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  (a.sameSide c BD) ∧ ¬(AB.intersectsLine CD) ∧ |(a─b)| = |(c─d)| →
  AC ≠ BD ∧ ¬(AC.intersectsLine BD) ∧ |(a─c)|= |(b─d)| := by
  euclid_intros
  euclid_intro_sentence "1.33.0"
    "Straight-lines joining equal and parallel (straight-lines) on the same sides are  themselves also equal and parallel.  Let $AB$ and $CD$ be equal and parallel (straight-lines), and let the straight-lines $AC$ and $BD$ join them on the same sides. I say that $AC$ and $BD$ are also equal and parallel. "

  euclid_apply (line_from_points b c) as BC
  euclid_sentence "1.33.1"
    "Let $BC$ have been joined."
    (step1 : distinctPointsOnLine b c BC) := by sorry

  -- @assumption_valid
  have step2_assumption1 : ¬(AB.intersectsLine CD) := by assumption
  -- @assumption_valid
  have step2_assumption2 : distinctPointsOnLine b c BC := by assumption
  -- @assumption ("$AB$ is parallel to $CD$", ¬(AB.intersectsLine CD))
  -- @assumption ("$BC$ has fallen across them", distinctPointsOnLine b c BC)
  euclid_sentence "1.33.2"
    "And since $AB$ is parallel to $CD$, and $BC$ has fallen across them, the alternate angles $ABC$ and $BCD$ are equal to one another [Prop.~1.29]."
    (step2 : ∠ a:b:c = ∠ b:c:d) := by sorry

  -- @assumption_valid
  have step3_assumption1 : |(a─b)| = |(c─d)| := by assumption
  -- @assumption_valid
  have step3_assumption2 : |(b─c)| = |(b─c)| := by rfl
  -- @assumption ("$AB$ is equal to $CD$", |(a─b)| = |(c─d)|)
  -- @assumption ("$BC$ is common", |(b─c)| = |(b─c)|)
  euclid_sentence "1.33.3"
    "And since $AB$ is equal to $CD$, and $BC$ is common, the two (straight-lines) $AB$, $BC$ are equal to the two (straight-lines) $DC$, $CB$.And the angle $ABC$ is equal to the angle $BCD$."
    (step3 : (|(a─b)| = |(d─c)| ∧ |(b─c)| = |(c─b)|) ∧ ∠ a:b:c = ∠ b:c:d) := by sorry

  euclid_sentence "1.33.4"
    "Thus, the base $AC$ is equal to the base $BD$,"
    (step4 : |(a─c)| = |(b─d)|) := by sorry

  euclid_sentence "1.33.5"
    "and triangle $ABC$ is equal to triangle $DCB$,"
    (step5 : Triangle.area △ a:b:c = Triangle.area △ d:c:b) := by sorry

  euclid_sentence "1.33.6"
    "and the remaining angles will be equal to the corresponding remaining angles subtended by the equal sides [Prop.~1.4]."
    (step6 : ∠ b:a:c = ∠ c:d:b ∧ ∠ a:c:b = ∠ d:b:c) := by sorry

  euclid_sentence "1.33.7"
    "Thus,  angle $ACB$  is equal to $CBD$."
    (step7 : ∠ a:c:b = ∠ c:b:d) := by sorry

  -- @assumption_valid
  have step8_assumption1 : ∠ a:c:b = ∠ c:b:d := by assumption
  -- @assumption ("the straight-line $BC$, (in) falling across the two straight-lines $AC$ and $BD$, has made the alternate angles  ($ACB$ and $CBD$) equal to one another", ∠ a:c:b = ∠ c:b:d)
  euclid_sentence "1.33.8"
    "Also, since the straight-line $BC$, (in) falling across the two straight-lines $AC$ and $BD$, has made the alternate angles  ($ACB$ and $CBD$) equal to one another, $AC$ is thus parallel to $BD$ [Prop.~1.27]."
    (step8 : ¬(AC.intersectsLine BD)) := by sorry

  euclid_sentence "1.33.9"
    "And ($AC$) was also shown (to be) equal to ($BD$). "
    (step9 : |(a─c)| = |(b─d)|) := by sorry

  have hAC_BD : AC ≠ BD := by sorry
  exact ⟨hAC_BD, step8, step9⟩
  euclid_conclude_sentence "1.33.10"
    "Thus, straight-lines joining equal and parallel (straight-lines) on the same sides are  themselves also equal and parallel. (Which is) the very thing it was required to show."

end Elements.Book1
