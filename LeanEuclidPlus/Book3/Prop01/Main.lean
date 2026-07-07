import SystemE
import Book1.Prop10.Main
import Book1.Prop11.Main
import Book3.Prop01.step1
import Book3.Prop01.step2
import Book3.Prop01.step3
import Book3.Prop01.step4
import Book3.Prop01.step5
import Book3.Prop01.step7
import Book3.Prop01.step8
import Book3.Prop01.step9
import Book3.Prop01.step10
import Book3.Prop01.step11
import Book3.Prop01.step12
import Book3.Prop01.step13
import Book3.Prop01.step14
import Book3.Prop01.step15
import Book3.Prop01.step16
import Book3.Prop01.step17
import Book3.Prop01.step18
import Book3.Prop01.step19
import Book3.Prop01.step20
import Book3.Prop01.hd_inside
import Book3.Prop01.hDC_int
import Book3.Prop01.hgNa
import Book3.Prop01.hgNd
import Book3.Prop01.hgNb
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

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
    (step1 : a.onCircle ABC ∧ b.onCircle ABC ∧ distinctPointsOnLine a b AB) := by euclid_apply (helper_3_1_step1 ABC a b AB (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)))

  euclid_apply (proposition_10 a b AB) as d
  -- @suppress_deps_check "Source edition (Fitzpatrick) brackets this segment-bisection as [Prop.~1.9], but 1.9 is angle-bisection; bisecting a straight-line is I.10 — the faithful construction applies proposition_10. Editorial bracket typo in the source, not ours."
  euclid_sentence "3.1.2"
    "and let ($AB$) be cut in half at point $D$ [Prop.~1.9]."
    (step2 : between a d b ∧ |(a─d)| = |(d─b)|) := by euclid_apply (helper_3_1_step2 a b d (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─b)|; assumption)))

  euclid_apply (proposition_11 a b d AB) as c0
  euclid_apply (line_from_points d c0) as DC
  -- Euclid's C, E are where the perpendicular meets the CIRCLE (not proposition_11's off-circle
  -- point): D is the midpoint of chord AB, hence inside ABC, so DC crosses the circle at C, E.
  -- This is what makes F = midpoint of CE the centre (CE is a diameter through the centre).
  have hd_inside : d.insideCircle ABC := by euclid_apply (helper_3_1_hd_inside ABC a b d (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show between a d b; assumption)))
  have hDC_int : DC.intersectsCircle ABC := by euclid_apply (helper_3_1_hDC_int ABC d DC (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)))
  euclid_apply (intersections_circle_line ABC DC) as (c, e)
  euclid_sentence "3.1.3"
    "And let $DC$ be drawn from $D$, at right-angles to $AB$ [Prop.~1.11]."
    (step3 : c.onCircle ABC ∧ ∠ a:d:c = ∟) := by euclid_apply (helper_3_1_step3 ABC a b c c0 d AB DC (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c0.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show ∠ a:d:c0 = ∟; assumption)) (by euclid_assumption "" (show ¬c0.onLine AB; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show d.insideCircle ABC; assumption)))

  euclid_sentence "3.1.4"
    "And let ($CD$) be drawn through to $E$."
    (step4 : e.onCircle ABC ∧ between c d e) := by euclid_apply (helper_3_1_step4 ABC c d e DC (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show e.onLine DC; assumption)) (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)))

  euclid_apply (proposition_10 c e DC) as f
  -- @suppress_deps_check "Same source bracket typo as 3.1.2: [Prop.~1.9] cited for cutting the straight-line CE in half, but segment-bisection is I.10 (1.9 is angle-bisection) — the construction applies proposition_10."
  euclid_sentence "3.1.5"
    "And let $CE$ be cut in half at $F$ [Prop.~1.9]."
    (step5 : between c f e ∧ |(c─f)| = |(f─e)|) := by euclid_apply (helper_3_1_step5 c e f (by euclid_assumption "" (show between c f e; assumption)) (by euclid_assumption "" (show |(c─f)| = |(f─e)|; assumption)))

  euclid_wts "3.1.6"
    "I say that (point) $F$ is the center of the [circle] $ABC$."

  euclid_apply (distinct_points f) as g
  have habsurd1 : ¬(g.isCentre ABC) := by
    intro hsuppose1
    have hgNa : g ≠ a := by euclid_apply (helper_3_1_hgNa ABC a g (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show g.isCentre ABC; assumption)))
    have hgNd : g ≠ d := by euclid_apply (helper_3_1_hgNd ABC a b c d e f g AB DC (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show between c d e; assumption)) (by euclid_assumption "" (show between c f e; assumption)) (by euclid_assumption "" (show |(c─f)| = |(f─e)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show e.onLine DC; assumption)) (by euclid_assumption "" (show g.isCentre ABC; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)))
    have hgNb : g ≠ b := by euclid_apply (helper_3_1_hgNb ABC b g (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show g.isCentre ABC; assumption)))
    euclid_apply (line_from_points g a) as GA
    euclid_apply (line_from_points g d) as GD
    euclid_apply (line_from_points g b) as GB
    euclid_sentence "3.1.7"
      "For (if) not (then), if possible, let $G$ (be the center of the circle),"
      (step7 : g.isCentre ABC) := by euclid_apply (helper_3_1_step7 ABC g (by euclid_assumption "" (show g.isCentre ABC; assumption)))

    euclid_sentence "3.1.8"
      "and let $GA$, $GD$, and $GB$ be joined."
      (step8 : distinctPointsOnLine g a GA ∧ distinctPointsOnLine g d GD ∧ distinctPointsOnLine g b GB) := by euclid_apply (helper_3_1_step8 g a d b GA GD GB (by euclid_assumption "" (show g.onLine GA; assumption)) (by euclid_assumption "" (show a.onLine GA; assumption)) (by euclid_assumption "" (show g.onLine GD; assumption)) (by euclid_assumption "" (show d.onLine GD; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)))

    -- @assumption_valid
    have step9_assumption1 : |(a─d)| = |(d─b)| := by assumption
    -- @assumption_valid
    have step9_assumption2 : |(d─g)| = |(d─g)| := by rfl
    -- @assumption ("$AD$ is equal to $DB$", |(a─d)| = |(d─b)|)
    -- @assumption ("$DG$ (is) common", |(d─g)| = |(d─g)|)
    euclid_sentence "3.1.9"
      "And since $AD$ is equal to $DB$, and $DG$ (is) common, the two (straight-lines) $AD$, $DG$ are equal to the two (straight-lines) $BD$, $DG$,$^\\dag$ respectively."
      (step9 : |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|) := by euclid_apply (helper_3_1_step9 a b d g (by euclid_assumption "$AD$ is equal to $DB$" (show |(a─d)| = |(d─b)|; assumption)) (by euclid_assumption "$DG$ (is) common" (show |(d─g)| = |(d─g)|; assumption)))

    -- @assumption_valid
    have step10_assumption1 : g.isCentre ABC ∧ a.onCircle ABC ∧ b.onCircle ABC := by euclid_finish
    -- @assumption ("For (they are both) radii", g.isCentre ABC ∧ a.onCircle ABC ∧ b.onCircle ABC)
    euclid_sentence "3.1.10"
      "And the base $GA$ is equal to the base $GB$. For (they are both) radii."
      (step10 : |(g─a)| = |(g─b)|) := by euclid_apply (helper_3_1_step10 ABC a b g (by euclid_assumption "For (they are both) radii" (show g.isCentre ABC ∧ a.onCircle ABC ∧ b.onCircle ABC; assumption)))

    euclid_sentence "3.1.11"
      "Thus, angle $ADG$ is equal to angle $GDB$ [Prop.~1.8]."
      (step11 : ∠ a:d:g = ∠ g:d:b) := by euclid_apply (helper_3_1_step11 a b d g AB GA GD GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine GA; assumption)) (by euclid_assumption "" (show a.onLine GA; assumption)) (by euclid_assumption "" (show g.onLine GD; assumption)) (by euclid_assumption "" (show d.onLine GD; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)) (by euclid_assumption "" (show |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|; assumption)) (by euclid_assumption "" (show |(g─a)| = |(g─b)|; assumption)))

    -- @assumption_valid
    have step12_assumption1 : ∠ a:d:g = ∠ g:d:b := by assumption
    -- @assumption ("a straight-line stood upon (another) straight-line make adjacent angles (which are) equal to one another", ∠ a:d:g = ∠ g:d:b)
    euclid_sentence "3.1.12"
      "And when a straight-line stood upon (another) straight-line make adjacent angles (which are) equal to one another, each of the equal angles is a right-angle [Def.~1.10]."
      (step12 : ∠ a:d:g = ∟ ∧ ∠ g:d:b = ∟) := by euclid_apply (helper_3_1_step12 a b d g AB GD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine GD; assumption)) (by euclid_assumption "" (show d.onLine GD; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)) (by euclid_assumption "" (show |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|; assumption)) (by euclid_assumption "" (show |(g─a)| = |(g─b)|; assumption)) (by euclid_assumption "a straight-line stood upon (another) straight-line make adjacent angles (which are) equal to one another" (show ∠ a:d:g = ∠ g:d:b; assumption)))

    euclid_sentence "3.1.13"
      "Thus, $GDB$ is a right-angle."
      (step13 : ∠ g:d:b = ∟) := by euclid_apply (helper_3_1_step13 a d g b (by euclid_assumption "" (show ∠ a:d:g = ∟ ∧ ∠ g:d:b = ∟; assumption)))

    euclid_sentence "3.1.14"
      "And $FDB$ is also a right-angle."
      (step14 : ∠ f:d:b = ∟) := by euclid_apply (helper_3_1_step14 ABC a b c c0 d e f g AB DC GD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show e.onLine DC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c0.onLine DC; assumption)) (by euclid_assumption "" (show ¬c0.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine GD; assumption)) (by euclid_assumption "" (show d.onLine GD; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show between c d e; assumption)) (by euclid_assumption "" (show between c f e; assumption)) (by euclid_assumption "" (show |(c─f)| = |(f─e)|; assumption)) (by euclid_assumption "" (show ∠ a:d:c = ∟; assumption)) (by euclid_assumption "" (show g.isCentre ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|; assumption)) (by euclid_assumption "" (show |(g─a)| = |(g─b)|; assumption)) (by euclid_assumption "" (show ∠ a:d:g = ∟ ∧ ∠ g:d:b = ∟; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)))

    euclid_sentence "3.1.15"
      "Thus, $FDB$ (is) equal to $GDB$, the greater to the lesser."
      (step15 : ∠ f:d:b = ∠ g:d:b) := by euclid_apply (helper_3_1_step15 f d g b (by euclid_assumption "" (show ∠ g:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ f:d:b = ∟; assumption)))

    euclid_sentence "3.1.16"
      "The very thing is impossible."
      (step16 : False) := by euclid_apply (helper_3_1_step16 ABC a b c d e f g AB DC GD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show e.onLine DC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show g.onLine GD; assumption)) (by euclid_assumption "" (show d.onLine GD; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show between c d e; assumption)) (by euclid_assumption "" (show between c f e; assumption)) (by euclid_assumption "" (show |(c─f)| = |(f─e)|; assumption)) (by euclid_assumption "" (show ∠ a:d:c = ∟; assumption)) (by euclid_assumption "" (show g.isCentre ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|; assumption)) (by euclid_assumption "" (show |(g─a)| = |(g─b)|; assumption)) (by euclid_assumption "" (show ∠ a:d:g = ∟ ∧ ∠ g:d:b = ∟; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)))
    exact step16

  euclid_sentence "3.1.17"
    "Thus, (point) $G$ is not the center of the circle $ABC$."
    (step17 : ¬(g.isCentre ABC)) := by euclid_apply (helper_3_1_step17 ABC g (by euclid_assumption "" (show ¬g.isCentre ABC; assumption)))

  euclid_sentence "3.1.18"
    "So, similarly, we can show that neither is any other (point) except $F$."
    (step18 : ∀ (g' : Point), g' ≠ f → ¬(g'.isCentre ABC)) := by euclid_apply (helper_3_1_step18 ABC a b c d e f AB DC (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show e.onLine DC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show between c d e; assumption)) (by euclid_assumption "" (show between c f e; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─b)|; assumption)) (by euclid_assumption "" (show |(c─f)| = |(f─e)|; assumption)) (by euclid_assumption "" (show ∠ a:d:c = ∟; assumption)))

  euclid_sentence "3.1.19"
    "Thus, point $F$ is the center of the [circle] $ABC$."
    (step19 : f.isCentre ABC) := by euclid_apply (helper_3_1_step19 ABC f (by euclid_assumption "" (show ∀ (g' : Point), g' ≠ f → ¬g'.isCentre ABC; assumption)))

  -- orchestrator-porism: corollary beyond the ∃f goal; specific instance for this figure
  euclid_sentence "3.1.20"
    "So, from this, (it is) manifest that if any straight-line in a circle cuts any (other) straight-line in half, and at right-angles, (then) the center of the circle is on the former (straight-line)."
    (step20 : f.onLine DC) := by euclid_apply (helper_3_1_step20 DC c e f (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show e.onLine DC; assumption)) (by euclid_assumption "" (show between c f e; assumption)))

  exact ⟨f, step19⟩
  euclid_conclude_sentence "3.1.21"
    "--- (Which is) the very thing it was required to do."

end Elements.Book3
