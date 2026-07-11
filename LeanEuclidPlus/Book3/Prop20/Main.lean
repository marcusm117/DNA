import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_20 : ∀ (a b c e : Point) (BC : Line) (ABC : Circle),
  e.isCentre ABC ∧
  a.onCircle ABC ∧
  b.onCircle ABC ∧
  c.onCircle ABC ∧
  distinctPointsOnLine b c BC ∧
  b ≠ a ∧
  c ≠ a ∧
  a.sameSide e BC →
  ∠ b:e:c = ∠ b:a:c + ∠ b:a:c :=
by
  euclid_intros
  euclid_intro_sentence "3.20.0"
    "In a circle, the angle at the center is double that at the circumference, when the angles have the same circumference base. Let $ABC$ be a circle, and let $BEC$ be an angle at its center, and $BAC$ (one) at (its) circumference. And let them have the same circumference base $BC$. I say that angle $BEC$ is double (angle) $BAC$."

  euclid_apply (line_from_points a e) as AEF
  euclid_apply (extend_point AEF a e) as f
  euclid_sentence "3.20.1"
    "For being joined, let $AE$ be drawn through to $F$."
    (step1 : distinctPointsOnLine a e AEF ∧ f.onCircle ABC ∧ between a e f) := by sorry

  -- @assumption_valid
  have step2_assumption1 : |(e─a)| = |(e─b)| := by euclid_finish
  -- @assumption ("$EA$ is equal to $EB$", |(e─a)| = |(e─b)|)
  euclid_sentence "3.20.2"
    "Therefore, since $EA$ is equal to $EB$, angle $EAB$ (is) also equal to $EBA$ [Prop.~1.5]."
    (step2 : ∠ e:a:b = ∠ e:b:a) := by sorry

  euclid_sentence "3.20.3"
    "Thus, angle $EAB$ and $EBA$ is double (angle) $EAB$."
    (step3 : ∠ e:a:b + ∠ e:b:a = ∠ e:a:b + ∠ e:a:b) := by sorry

  euclid_sentence "3.20.4"
    "And $BEF$ (is) equal to $EAB$ and $EBA$ [Prop.~1.32]."
    (step4 : ∠ b:e:f = ∠ e:a:b + ∠ e:b:a) := by sorry

  euclid_sentence "3.20.5"
    "Thus, $BEF$ is also double $EAB$."
    (step5 : ∠ b:e:f = ∠ e:a:b + ∠ e:a:b) := by sorry

  euclid_sentence "3.20.6"
    "So, for the same (reasons), $FEC$ is also double $EAC$."
    (step6 : ∠ f:e:c = ∠ e:a:c + ∠ e:a:c) := by sorry

  euclid_sentence "3.20.7"
    "Thus, the whole (angle) $BEC$ is double the whole (angle) $BAC$."
    (step7 : ∠ b:e:c = ∠ b:a:c + ∠ b:a:c) := by sorry

  have hd_ex : ∃ d : Point, d.onCircle ABC ∧ b ≠ d ∧ c ≠ d ∧ a ≠ d := by sorry
  obtain ⟨d, hd_on, hdb, hdc, hda⟩ := hd_ex
  euclid_sentence "3.20.8"
    "So let another (straight-line) be inflected, and let there be another angle, $BDC$."
    (step8 : d.onCircle ABC ∧ b ≠ d ∧ c ≠ d ∧ a ≠ d) := by sorry

  euclid_apply (line_from_points d e) as DEG
  euclid_apply (extend_point DEG d e) as g
  euclid_sentence "3.20.9"
    "And $DE$ being joined, let it be produced to $G$."
    (step9 : distinctPointsOnLine d e DEG ∧ g.onCircle ABC ∧ between d e g) := by sorry

  euclid_sentence "3.20.10"
    "So, similarly, we can show that angle $GEC$ is double $EDC$,"
    (step10 : ∠ g:e:c = ∠ e:d:c + ∠ e:d:c) := by sorry

  euclid_sentence "3.20.11"
    "of which $GEB$ is double $EDB$."
    (step11 : ∠ g:e:b = ∠ e:d:b + ∠ e:d:b) := by sorry

  euclid_sentence "3.20.12"
    "Thus, the remaining (angle) $BEC$ is double the (remaining angle) $BDC$."
    (step12 : ∠ b:e:c = ∠ b:d:c + ∠ b:d:c) := by sorry

  exact step7
  euclid_conclude_sentence "3.20.13"
    "Thus, in a circle, the angle at the center is double that at the circumference, when [the angles] have the same circumference base. (Which is) the very thing it was required to show."

end Elements.Book3
