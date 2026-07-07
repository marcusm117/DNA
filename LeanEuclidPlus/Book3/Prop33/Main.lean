import SystemE
import Book1.Prop10.Main
import Book1.Prop11.Main
import Book1.Prop23.Main
import Book3.Prop16.Main
import Book3.Prop31.Main
import Book3.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

-- orchestrator-3case: trichotomy on ∠ c₁:c:c₂ vs ∟ splits into three branches (acute/right/obtuse);
-- each branch constructs its circle and witness point, closes the ∃-goal with exact stepN.
-- wts at 3.33.18 opens case 2 inside its branch; wts at 3.33.27 opens case 3.
set_option systemE.solverTime 30 in
theorem proposition_33 : ∀ (a b c₁ c c₂ : Point),
  a ≠ b →
  ∃ (α : Circle) (e : Point), a.onCircle α ∧ b.onCircle α ∧ e.onCircle α ∧ ∠ a:e:b = ∠ c₁:c:c₂ :=
by
  euclid_intros
  euclid_intro_sentence "3.33.0"
    "To draw a segment of a circle, accepting an angle equal to a given rectilinear angle, on a given straight-line. Let $AB$ be the given straight-line, and $C$ the given rectilinear angle. So it is required to draw a segment of a circle, accepting an angle equal to $C$, on the given straight-line $AB$. So the [angle] $C$ is surely either acute, a right-angle, or obtuse. First of all, let it be acute."

  rcases lt_trichotomy (∠ c₁:c:c₂) ∟ with hacute | hright | hobtuse

  · -- ── CASE 1 : ∠ c₁:c:c₂ < ∟  (acute) ─────────────────────────────────────────
    -- Construction witnesses (Phase A: exact euclid_apply calls deferred to Phase B)
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = angle C at A on AB [Prop 1.23]
    have hd_ex : ∃ d : Point, ∠ b:a:d = ∠ c₁:c:c₂ ∧ ¬d.onLine AB := by sorry
    obtain ⟨d, hd_ang, hd_off⟩ := hd_ex
    euclid_apply (line_from_points a d) as AD
    -- AE at right-angles to DA at A [Prop 1.11]
    have he_ex : ∃ e : Point, ¬e.onLine AD ∧ ∠ d:a:e = ∟ := by sorry
    obtain ⟨e, he_off, he_perp⟩ := he_ex
    euclid_apply (line_from_points a e) as AE
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    -- FG at right-angles to AB at F [Prop 1.11]; G on line AE
    have hg_ex : ∃ g : Point, g.onLine AE ∧ ∠ a:f:g = ∟ := by sorry
    obtain ⟨g, hg_ae, hg_perp⟩ := hg_ex
    euclid_apply (line_from_points f g) as FG
    have hgb : g ≠ b := by sorry
    euclid_apply (line_from_points g b) as GB
    -- Circle with center G, radius GA
    have hga : g ≠ a := by sorry
    euclid_apply (circle_from_points g a) as α
    -- B and E also lie on this circle (proved via AG = BG from SAS)
    have hb_circ : b.onCircle α := by sorry
    have he_circ : e.onCircle α := by sorry
    -- EB joined
    have heb : e ≠ b := by sorry
    euclid_apply (line_from_points e b) as EB

    euclid_sentence "3.33.1"
      "And, as in the first diagram (from the left), let (angle) $BAD$, equal to angle $C$, be constructed on the straight-line $AB$, at the point A (on it) [Prop.~1.23]."
      (step1 : ∠ b:a:d = ∠ c₁:c:c₂) := by sorry

    euclid_sentence "3.33.2"
      "Thus, $BAD$ is also acute."
      (step2 : ∠ b:a:d < ∟) := by sorry

    euclid_sentence "3.33.3"
      "Let $AE$ be drawn, at right-angles to $DA$ [Prop.~1.11]."
      (step3 : ∠ d:a:e = ∟) := by sorry

    euclid_sentence "3.33.4"
      "And let $AB$ be cut in half at $F$ [Prop.~1.10]."
      (step4 : between a f b ∧ |(a─f)| = |(f─b)|) := by sorry

    euclid_sentence "3.33.5"
      "And let $FG$ be drawn from point $F$, at right-angles to $AB$ [Prop.~1.11]."
      (step5 : ∠ a:f:g = ∟) := by sorry

    euclid_sentence "3.33.6"
      "And let $GB$ be joined."
      (step6 : distinctPointsOnLine g b GB) := by sorry

    -- @assumption ("$AF$ is equal to $FB$", |(a─f)| = |(f─b)|)
    -- @assumption ("$FG$ (is) common", |(f─g)| = |(f─g)|)
    euclid_sentence "3.33.7"
      "And since $AF$ is equal to $FB$, and $FG$ (is) common, the two (straight-lines) $AF$, $FG$ are equal to the two (straight-lines) $BF$, $FG$ (respectively)."
      (step7 : |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)|) := by sorry

    euclid_sentence "3.33.8"
      "And angle $AFG$ (is) equal to [angle] $BFG$."
      (step8 : ∠ a:f:g = ∠ b:f:g) := by sorry

    euclid_sentence "3.33.9"
      "Thus, the base $AG$ is equal to the base $BG$ [Prop.~1.4]."
      (step9 : |(a─g)| = |(b─g)|) := by sorry

    euclid_sentence "3.33.10"
      "Thus, the circle drawn with center $G$, and radius $GA$, will also go through $B$ (as well as $A$)."
      (step10 : a.onCircle α ∧ b.onCircle α) := by sorry

    euclid_sentence "3.33.11"
      "Let it be drawn, and let it be (denoted) $ABE$."
      (step11 : g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ e.onCircle α) := by sorry

    euclid_sentence "3.33.12"
      "And let $EB$ be joined."
      (step12 : distinctPointsOnLine e b EB) := by sorry

    -- @assumption ("$AD$ is at the extremity of diameter $AE$, (namely, point) $A$, at right-angles to $AE$", ∠ d:a:e = ∟)
    euclid_sentence "3.33.13"
      "Therefore, since $AD$ is at the extremity of diameter $AE$, (namely, point) $A$, at right-angles to $AE$, the (straight-line) $AD$ thus touches the circle $ABE$ [Prop.~3.16~corr.]."
      (step13 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by sorry

    -- @assumption ("some straight-line $AD$ touches the circle $ABE$", (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α)
    -- @assumption ("some (other) straight-line $AB$ has been drawn across from the point of contact $A$ into circle $ABE$", a.onLine AB ∧ b.onLine AB ∧ b.onCircle α)
    euclid_sentence "3.33.14"
      "Therefore, since some straight-line $AD$ touches the circle $ABE$, and some (other) straight-line $AB$ has been drawn across from the point of contact $A$ into circle $ABE$, angle $DAB$ is thus equal to the angle $AEB$ in the alternate segment of the circle [Prop.~3.32]."
      (step14 : ∠ d:a:b = ∠ a:e:b) := by sorry

    euclid_sentence "3.33.15"
      "But, $DAB$ is equal to $C$."
      (step15 : ∠ d:a:b = ∠ c₁:c:c₂) := by sorry

    euclid_sentence "3.33.16"
      "Thus, angle $C$ is also equal to $AEB$."
      (step16 : ∠ c₁:c:c₂ = ∠ a:e:b) := by sorry

    euclid_sentence "3.33.17"
      "Thus, a segment $AEB$ of a circle, accepting the angle $AEB$ (which is) equal to the given (angle) $C$, has been drawn on the given straight-line $AB$."
      (step17 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by sorry

    exact step17

  · -- ── CASE 2 : ∠ c₁:c:c₂ = ∟  (right angle) ─────────────────────────────────────
    euclid_wts "3.33.18"
      "And so let $C$ be a right-angle. And let it again be necessary to draw a segment of a circle on $AB$, accepting an angle equal to the right-[angle] $C$."

    -- Construction witnesses
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = right-angle C at A on AB [Prop 1.23]
    have hd_ex : ∃ d : Point, ∠ b:a:d = ∠ c₁:c:c₂ ∧ ¬d.onLine AB := by sorry
    obtain ⟨d, hd_ang, hd_off⟩ := hd_ex
    euclid_apply (line_from_points a d) as AD
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    have hfa : f ≠ a := by sorry
    -- Circle AEB with center F, radius FA (= FB since F is midpoint)
    euclid_apply (circle_from_points f a) as α
    have hb_circ : b.onCircle α := by sorry
    -- E: a point on circle α not on AB (in the semicircle)
    have he_ex : ∃ e : Point, e.onCircle α ∧ ¬e.onLine AB := by sorry
    obtain ⟨e, he_circ, he_off⟩ := he_ex

    euclid_sentence "3.33.19"
      "Let the (angle) $BAD$ [again] be constructed, equal to the right-angle $C$ [Prop.~1.23], as in the second diagram (from the left)."
      (step19 : ∠ b:a:d = ∠ c₁:c:c₂) := by sorry

    euclid_sentence "3.33.20"
      "And let $AB$ be cut in half at $F$ [Prop.~1.10]."
      (step20 : between a f b ∧ |(a─f)| = |(f─b)|) := by sorry

    euclid_sentence "3.33.21"
      "And let the circle $AEB$ be drawn with center $F$, and radius either $FA$ or $FB$."
      (step21 : f.isCentre α ∧ a.onCircle α ∧ b.onCircle α) := by sorry

    -- @assumption ("the angle at $A$ being a right-angle", ∠ b:a:d = ∟)
    euclid_sentence "3.33.22"
      "Thus, the straight-line $AD$ touches the circle $ABE$, on account of the angle at $A$ being a right-angle [Prop.~3.16 corr.]."
      (step22 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by sorry

    -- @assumption ("(the latter angle), being in a semi-circle, is also a right-angle", ∠ a:e:b = ∟)
    euclid_sentence "3.33.23"
      "And angle $BAD$ is equal to the angle in segment $AEB$. For (the latter angle), being in a semi-circle, is also a right-angle [Prop.~3.31]."
      (step23 : ∠ b:a:d = ∠ a:e:b) := by sorry

    euclid_sentence "3.33.24"
      "But, $BAD$ is also equal to $C$."
      (step24 : ∠ b:a:d = ∠ c₁:c:c₂) := by sorry

    euclid_sentence "3.33.25"
      "Thus, the (angle) in (segment) $AEB$ is also equal to $C$."
      (step25 : ∠ a:e:b = ∠ c₁:c:c₂) := by sorry

    euclid_sentence "3.33.26"
      "Thus, a segment $AEB$ of a circle, accepting an angle equal to $C$, has again been drawn on $AB$."
      (step26 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by sorry

    exact step26

  · -- ── CASE 3 : ∟ < ∠ c₁:c:c₂  (obtuse) ─────────────────────────────────────────
    euclid_wts "3.33.27"
      "And so let (angle) $C$ be obtuse."

    -- Construction witnesses
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = obtuse angle C at A on AB [Prop 1.23]
    have hd_ex : ∃ d : Point, ∠ b:a:d = ∠ c₁:c:c₂ ∧ ¬d.onLine AB := by sorry
    obtain ⟨d, hd_ang, hd_off⟩ := hd_ex
    euclid_apply (line_from_points a d) as AD
    -- AE at right-angles to AD at A [Prop 1.11]
    have he_ex : ∃ e : Point, ¬e.onLine AD ∧ ∠ d:a:e = ∟ := by sorry
    obtain ⟨e, he_off, he_perp⟩ := he_ex
    euclid_apply (line_from_points a e) as AE
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    -- FG at right-angles to AB at F [Prop 1.11]
    have hg_ex : ∃ g : Point, ¬g.onLine AB ∧ ∠ a:f:g = ∟ := by sorry
    obtain ⟨g, hg_off, hg_perp⟩ := hg_ex
    euclid_apply (line_from_points f g) as FG
    have hgb : g ≠ b := by sorry
    euclid_apply (line_from_points g b) as GB
    -- Circle with center G, radius GA
    have hga : g ≠ a := by sorry
    euclid_apply (circle_from_points g a) as α
    have hb_circ : b.onCircle α := by sorry
    -- H: a point on the circle in the alternate segment AHB (opposite side of AB from D)
    have hh_ex : ∃ h : Point, h.onCircle α ∧ h.opposingSides d AB := by sorry
    obtain ⟨h, hh_circ, hh_side⟩ := hh_ex

    euclid_sentence "3.33.28"
      "And let (angle) $BAD$, equal to ($C$), be constructed on the straight-line $AB$, at the point $A$ (on it) [Prop.~1.23], as in the third diagram (from the left)."
      (step28 : ∠ b:a:d = ∠ c₁:c:c₂) := by sorry

    euclid_sentence "3.33.29"
      "And let $AE$ be drawn, at right-angles to $AD$ [Prop.~1.11]."
      (step29 : ∠ d:a:e = ∟) := by sorry

    euclid_sentence "3.33.30"
      "And let $AB$ again be cut in half at $F$ [Prop.~1.10]."
      (step30 : between a f b ∧ |(a─f)| = |(f─b)|) := by sorry

    euclid_sentence "3.33.31"
      "And let $FG$ be drawn, at right-angles to $AB$ [Prop.~1.10]."
      (step31 : ∠ a:f:g = ∟) := by sorry

    euclid_sentence "3.33.32"
      "And let $GB$ be joined."
      (step32 : distinctPointsOnLine g b GB) := by sorry

    -- @assumption ("$AF$ is equal to $FB$", |(a─f)| = |(f─b)|)
    -- @assumption ("$FG$ (is) common", |(f─g)| = |(f─g)|)
    euclid_sentence "3.33.33"
      "And again, since $AF$ is equal to $FB$, and $FG$ (is) common, the two (straight-lines) $AF$, $FG$ are equal to the two (straight-lines) $BF$, $FG$ (respectively)."
      (step33 : |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)|) := by sorry

    euclid_sentence "3.33.34"
      "And angle $AFG$ (is) equal to angle $BFG$."
      (step34 : ∠ a:f:g = ∠ b:f:g) := by sorry

    euclid_sentence "3.33.35"
      "Thus, the base $AG$ is equal to the base $BG$ [Prop.~1.4]."
      (step35 : |(a─g)| = |(b─g)|) := by sorry

    euclid_sentence "3.33.36"
      "Thus, a circle of center $G$, and radius $GA$, being drawn, will also go through $B$ (as well as $A$)."
      (step36 : a.onCircle α ∧ b.onCircle α) := by sorry

    euclid_sentence "3.33.37"
      "Let it go like $AEB$ (in the third diagram from the left)."
      (step37 : g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ h.onCircle α) := by sorry

    -- @assumption ("$AD$ is at right-angles to the diameter $AE$, at its extremity", ∠ d:a:e = ∟)
    euclid_sentence "3.33.38"
      "And since $AD$ is at right-angles to the diameter $AE$, at its extremity, $AD$ thus touches circle $AEB$ [Prop.~3.16~corr.]."
      (step38 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by sorry

    -- @assumption ("$AB$ has been drawn across (the circle) from the point of contact $A$", a.onLine AB ∧ b.onLine AB ∧ b.onCircle α)
    euclid_sentence "3.33.39"
      "And $AB$ has been drawn across (the circle) from the point of contact $A$. Thus, angle $BAD$ is equal to the angle constructed in the alternate segment $AHB$ of the circle [Prop.~3.32]."
      (step39 : ∠ b:a:d = ∠ a:h:b) := by sorry

    euclid_sentence "3.33.40"
      "But, angle $BAD$ is equal to $C$."
      (step40 : ∠ b:a:d = ∠ c₁:c:c₂) := by sorry

    euclid_sentence "3.33.41"
      "Thus, the angle in segment $AHB$ is also equal to $C$."
      (step41 : ∠ a:h:b = ∠ c₁:c:c₂) := by sorry

    euclid_sentence "3.33.42"
      "Thus, a segment $AHB$ of a circle, accepting an angle equal to $C$, has been drawn on the given straight-line $AB$."
      (step42 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by sorry

    exact step42

  euclid_conclude_sentence "3.33.43"
    "(Which is) the very thing it was required to do."

end Elements.Book3
