import SystemE
import Book.Prop10
import Book.Prop11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_1 : ∀ (ABC : Circle),
  ∃ f : Point, f.isCentre ABC :=
by
  euclid_intros
  euclid_intro_sentence "3.1.0"
    "To find the center of a given circle. Let $ABC$ be the given circle. So it is required to find the center of circle $ABC$."

  euclid_apply (exists_point_on_circle ABC) as a
  euclid_apply (exists_distinct_point_on_circle ABC a) as b
  euclid_apply (line_from_points a b) as AB
  euclid_sentence "3.1.1"
    "Let some straight-line $AB$ be drawn through ($ABC$), at random,"
    (step1 : a.onCircle ABC ∧ b.onCircle ABC ∧ distinctPointsOnLine a b AB) := by sorry

  euclid_apply (proposition_10 a b AB) as d
  euclid_sentence "3.1.2"
    "and let ($AB$) be cut in half at point $D$ [Prop.~1.9]."
    (step2 : between a d b ∧ |(a─d)| = |(d─b)|) := by sorry

  euclid_apply (proposition_11 a b d AB) as c
  euclid_apply (line_from_points d c) as DC
  euclid_sentence "3.1.3"
    "And let $DC$ be drawn from $D$, at right-angles to $AB$ [Prop.~1.11]."
    (step3 : ¬(c.onLine AB) ∧ ∠ a:d:c = ∟) := by sorry

  euclid_apply (extend_point DC c d) as e
  euclid_sentence "3.1.4"
    "And let ($CD$) be drawn through to $E$."
    (step4 : between c d e) := by sorry

  euclid_apply (proposition_10 c e DC) as f
  euclid_sentence "3.1.5"
    "And let $CE$ be cut in half at $F$ [Prop.~1.9]."
    (step5 : between c f e ∧ |(c─f)| = |(f─e)|) := by sorry

  euclid_wts "3.1.6"
    "I say that (point) $F$ is the center of the [circle] $ABC$."

  euclid_apply (distinct_points f) as g
  have habsurd1 : ¬(g.isCentre ABC) := by
    intro hsuppose1
    have hgNa : g ≠ a := by sorry
    have hgNd : g ≠ d := by sorry
    have hgNb : g ≠ b := by sorry
    euclid_apply (line_from_points g a) as GA
    euclid_apply (line_from_points g d) as GD
    euclid_apply (line_from_points g b) as GB
    euclid_sentence "3.1.7"
      "For (if) not (then), if possible, let $G$ (be the center of the circle),"
      (step7 : g.isCentre ABC) := by sorry

    euclid_sentence "3.1.8"
      "and let $GA$, $GD$, and $GB$ be joined."
      (step8 : distinctPointsOnLine g a GA ∧ distinctPointsOnLine g d GD ∧ distinctPointsOnLine g b GB) := by sorry

    -- @assumption ("$AD$ is equal to $DB$", |(a─d)| = |(d─b)|)
    -- @assumption ("$DG$ (is) common", |(d─g)| = |(d─g)|)
    euclid_sentence "3.1.9"
      "And since $AD$ is equal to $DB$, and $DG$ (is) common, the two (straight-lines) $AD$, $DG$ are equal to the two (straight-lines) $BD$, $DG$,$^\\dag$ respectively."
      (step9 : |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|) := by sorry

    -- @assumption ("For (they are both) radii", g.isCentre ABC ∧ a.onCircle ABC ∧ b.onCircle ABC)
    euclid_sentence "3.1.10"
      "And the base $GA$ is equal to the base $GB$. For (they are both) radii."
      (step10 : |(g─a)| = |(g─b)|) := by sorry

    euclid_sentence "3.1.11"
      "Thus, angle $ADG$ is equal to angle $GDB$ [Prop.~1.8]."
      (step11 : ∠ a:d:g = ∠ g:d:b) := by sorry

    -- @assumption ("a straight-line stood upon (another) straight-line make adjacent angles (which are) equal to one another", ∠ a:d:g = ∠ g:d:b)
    euclid_sentence "3.1.12"
      "And when a straight-line stood upon (another) straight-line make adjacent angles (which are) equal to one another, each of the equal angles is a right-angle [Def.~1.10]."
      (step12 : ∠ a:d:g = ∟ ∧ ∠ g:d:b = ∟) := by sorry

    euclid_sentence "3.1.13"
      "Thus, $GDB$ is a right-angle."
      (step13 : ∠ g:d:b = ∟) := by sorry

    euclid_sentence "3.1.14"
      "And $FDB$ is also a right-angle."
      (step14 : ∠ f:d:b = ∟) := by sorry

    euclid_sentence "3.1.15"
      "Thus, $FDB$ (is) equal to $GDB$, the greater to the lesser."
      (step15 : ∠ f:d:b = ∠ g:d:b) := by sorry

    euclid_sentence "3.1.16"
      "The very thing is impossible."
      (step16 : False) := by sorry
    exact step16

  euclid_sentence "3.1.17"
    "Thus, (point) $G$ is not the center of the circle $ABC$."
    (step17 : ¬(g.isCentre ABC)) := by sorry

  euclid_sentence "3.1.18"
    "So, similarly, we can show that neither is any other (point) except $F$."
    (step18 : ∀ (g' : Point), g' ≠ f → ¬(g'.isCentre ABC)) := by sorry

  euclid_sentence "3.1.19"
    "Thus, point $F$ is the center of the [circle] $ABC$."
    (step19 : f.isCentre ABC) := by sorry

  -- orchestrator-porism: corollary beyond the ∃f goal; specific instance for this figure
  euclid_sentence "3.1.20"
    "So, from this, (it is) manifest that if any straight-line in a circle cuts any (other) straight-line in half, and at right-angles, (then) the center of the circle is on the former (straight-line)."
    (step20 : f.onLine DC) := by sorry

  exact ⟨f, step19⟩
  euclid_conclude_sentence "3.1.21"
    "--- (Which is) the very thing it was required to do."

end Elements.Book3
