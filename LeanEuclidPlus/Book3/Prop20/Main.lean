import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_20 : ∀ (a b c e : Point) (AB : Line) (ABC : Circle),
  e.isCentre ABC ∧
  a.onCircle ABC ∧
  b.onCircle ABC ∧
  c.onCircle ABC ∧
  distinctPointsOnLine a b AB ∧
  a ≠ c ∧
  b ≠ c ∧
  c.sameSide e AB →
  ∠ a:e:b = ∠ a:c:b + ∠ a:c:b :=
by
  euclid_intros
  euclid_intro_sentence "3.20.0"
    "In a circle, the angle at the center is double that at the circumference, when the angles have the same circumference base. Let $ABC$ be a circle, and let $BEC$ be an angle at its center, and $BAC$ (one) at (its) circumference. And let them have the same circumference base $BC$. I say that angle $BEC$ is double (angle) $BAC$."

  euclid_apply (line_from_points c e) as AEF
  euclid_apply (extend_point AEF c e) as f
  euclid_sentence "3.20.1"
    "For being joined, let $AE$ be drawn through to $F$."
    (step1 : distinctPointsOnLine c e AEF ∧ f.onCircle ABC ∧ between c e f) := by sorry

  -- @assumption ("$EA$ is equal to $EB$", |(e─c)| = |(e─a)|)
  euclid_sentence "3.20.2"
    "Therefore, since $EA$ is equal to $EB$, angle $EAB$ (is) also equal to $EBA$ [Prop.~1.5]."
    (step2 : ∠ e:c:a = ∠ e:a:c) := by sorry

  euclid_sentence "3.20.3"
    "Thus, angle $EAB$ and $EBA$ is double (angle) $EAB$."
    (step3 : ∠ e:c:a + ∠ e:a:c = ∠ e:c:a + ∠ e:c:a) := by sorry

  euclid_sentence "3.20.4"
    "And $BEF$ (is) equal to $EAB$ and $EBA$ [Prop.~1.32]."
    (step4 : ∠ a:e:f = ∠ e:c:a + ∠ e:a:c) := by sorry

  euclid_sentence "3.20.5"
    "Thus, $BEF$ is also double $EAB$."
    (step5 : ∠ a:e:f = ∠ e:c:a + ∠ e:c:a) := by sorry

  euclid_sentence "3.20.6"
    "So, for the same (reasons), $FEC$ is also double $EAC$."
    (step6 : ∠ f:e:b = ∠ e:c:b + ∠ e:c:b) := by sorry

  euclid_sentence "3.20.7"
    "Thus, the whole (angle) $BEC$ is double the whole (angle) $BAC$."
    (step7 : ∠ a:e:b = ∠ a:c:b + ∠ a:c:b) := by sorry

  -- orchestrator-note: case 2 introduces d as a second inscribed vertex (D in Euclid text).
  -- step7 proves the goal for c (case 1). Steps 8-12 faithfully map case 2 for d; they are
  -- in-scope haves and do not affect the final `exact step7`. Phase B must prove step7 for
  -- ALL configurations of c (both geometric sub-cases) within its backing file.
  have hd_ex : ∃ d : Point, d.onCircle ABC ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d := by sorry
  obtain ⟨d, hd_on, hda, hdb, hdc⟩ := hd_ex
  euclid_sentence "3.20.8"
    "So let another (straight-line) be inflected, and let there be another angle, $BDC$."
    (step8 : d.onCircle ABC ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d) := by sorry

  euclid_apply (line_from_points d e) as DEG
  euclid_apply (extend_point DEG d e) as g
  euclid_sentence "3.20.9"
    "And $DE$ being joined, let it be produced to $G$."
    (step9 : distinctPointsOnLine d e DEG ∧ g.onCircle ABC ∧ between d e g) := by sorry

  euclid_sentence "3.20.10"
    "So, similarly, we can show that angle $GEC$ is double $EDC$,"
    (step10 : ∠ g:e:b = ∠ e:d:b + ∠ e:d:b) := by sorry

  euclid_sentence "3.20.11"
    "of which $GEB$ is double $EDB$."
    (step11 : ∠ g:e:a = ∠ e:d:a + ∠ e:d:a) := by sorry

  euclid_sentence "3.20.12"
    "Thus, the remaining (angle) $BEC$ is double the (remaining angle) $BDC$."
    (step12 : ∠ a:e:b = ∠ a:d:b + ∠ a:d:b) := by sorry

  exact step7
  euclid_conclude_sentence "3.20.13"
    "Thus, in a circle, the angle at the center is double that at the circumference, when [the angles] have the same circumference base. (Which is) the very thing it was required to show."

end Elements.Book3
