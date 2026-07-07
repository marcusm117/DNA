import SystemE
import Book1.Prop10.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_9 : ∀ (ABC : Circle) (a b c d : Point),
    d.insideCircle ABC ∧
    a.onCircle ABC ∧ b.onCircle ABC ∧ c.onCircle ABC ∧
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| →
    d.isCentre ABC :=
by
  euclid_intros
  euclid_intro_sentence "3.9.0"
    "If some point is taken inside a circle, and more than two equal straight-lines radiate from the point towards the (circumference of the) circle, (then) the point taken is the center of the circle. Let $ABC$ be a circle, and $D$ a point inside it, and let more than two equal straight-lines, $DA$, $DB$, and $DC$, radiate from $D$ towards (the circumference of) circle $ABC$. I say that point $D$ is the center of circle $ABC$."

  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points b c) as BC
  euclid_apply (proposition_10 a b AB) as e
  euclid_apply (proposition_10 b c BC) as f
  euclid_sentence "3.9.1"
    "For let $AB$ and $BC$ be joined, and (then) be cut in half at points $E$ and $F$ (respectively) [Prop.~1.10]."
    (step1 : distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
             between a e b ∧ |(a─e)| = |(e─b)| ∧ between b f c ∧ |(b─f)| = |(f─c)|) := by sorry

  -- @euclid_gap (generic-position): Euclid draws AB, BC as generic chords and reads E, F ≠ D off
  -- the figure. When a chord is a DIAMETER its midpoint equals the centre = D (E = D or F = D), and
  -- the perpendicular bisector GK / HL degenerates. Those two cases are split off here — D is then
  -- directly the centre (equidistant from A, B, C). At most one occurs (AB, BC share B; two diameters
  -- would meet at the centre = B, impossible as B is on the circle). Generic branch = Euclid's argument.
  by_cases h_ed : e = d
  · -- @euclid_gap: AB is a diameter ⟹ E = D = centre; D is directly the centre (equidistant A,B,C)
    have hcentre : d.isCentre ABC := by sorry
    exact hcentre
  · by_cases h_fd : f = d
    · -- @euclid_gap: BC is a diameter ⟹ F = D = centre; D is directly the centre
      have hcentre : d.isCentre ABC := by sorry
      exact hcentre
    · have he_ne_d : e ≠ d := h_ed
      have hf_ne_d : f ≠ d := h_fd
      euclid_apply (line_from_points e d) as GK
      euclid_apply (line_from_points f d) as HL
      have hg_ex : ∃ g : Point, g.onCircle ABC ∧ g.onLine GK := by sorry
      obtain ⟨g, hg_on_circle, hg_on_GK⟩ := hg_ex
      have hk_ex : ∃ k : Point, k.onCircle ABC ∧ k.onLine GK ∧ k ≠ g := by sorry
      obtain ⟨k, hk_on_circle, hk_on_GK, hk_ne_g⟩ := hk_ex
      have hh_ex : ∃ h : Point, h.onCircle ABC ∧ h.onLine HL := by sorry
      obtain ⟨h, hh_on_circle, hh_on_HL⟩ := hh_ex
      have hl_ex : ∃ l : Point, l.onCircle ABC ∧ l.onLine HL ∧ l ≠ h := by sorry
      obtain ⟨l, hl_on_circle, hl_on_HL, hl_ne_h⟩ := hl_ex
      euclid_sentence "3.9.2"
        "And $ED$ and $FD$ being joined, let them be drawn through to points $G$, $K$, $H$, and $L$."
        (step2 : e.onLine GK ∧ d.onLine GK ∧ f.onLine HL ∧ d.onLine HL ∧
                 g.onCircle ABC ∧ k.onCircle ABC ∧ g.onLine GK ∧ k.onLine GK ∧
                 h.onCircle ABC ∧ l.onCircle ABC ∧ h.onLine HL ∧ l.onLine HL) := by sorry

      -- @assumption ("$AE$ is equal to $EB$", |(a─e)| = |(e─b)|)
      -- @assumption ("$ED$ (is) common", |(e─d)| = |(e─d)|)
      euclid_sentence "3.9.3"
        "Therefore, since $AE$ is equal to $EB$, and $ED$ (is) common, the two (straight-lines) $AE$, $ED$ are equal to the two (straight-lines) $BE$, $ED$ (respectively)."
        (step3 : |(a─e)| = |(b─e)| ∧ |(e─d)| = |(e─d)|) := by sorry

      -- orchestrator-hypothesis: DA=DB is theorem hypothesis |(d─a)| = |(d─b)|; Euclid cites it explicitly for the I.8 SAS argument; RULE 2 tension acknowledged
      euclid_sentence "3.9.4"
        "And the base $DA$ (is) equal to the base $DB$."
        (step4 : |(d─a)| = |(d─b)|) := by sorry

      euclid_sentence "3.9.5"
        "Thus, angle $AED$ is equal to angle $BED$ [Prop.~1.8]."
        (step5 : ∠ a:e:d = ∠ b:e:d) := by sorry

      euclid_sentence "3.9.6"
        "Thus, angles $AED$ and $BED$ (are) each right-angles [Def.~1.10]."
        (step6 : ∠ a:e:d = ∟ ∧ ∠ b:e:d = ∟) := by sorry

      euclid_sentence "3.9.7"
        "Thus, $GK$ cuts $AB$ in half,"
        (step7 : e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)|) := by sorry

      euclid_sentence "3.9.8"
        "and at right-angles."
        (step8 : ∠ a:e:d = ∟) := by sorry

      -- @assumption ("if some straight-line in a circle cuts some (other) straight-line in half, and at right-angles, (then) the center of the circle is on the former (straight-line)", e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧ ∠ a:e:d = ∟ → ∀ o : Point, o.isCentre ABC → o.onLine GK)
      euclid_sentence "3.9.9"
        "And since, if some straight-line in a circle cuts some (other) straight-line in half, and at right-angles, (then) the center of the circle is on the former (straight-line) [Prop.~3.1~corr.], the center of the circle is thus on $GK$."
        (step9 : ∀ o : Point, o.isCentre ABC → o.onLine GK) := by sorry

      euclid_sentence "3.9.10"
        "So, for the same (reasons), the center of circle $ABC$ is also on $HL$."
        (step10 : ∀ o : Point, o.isCentre ABC → o.onLine HL) := by sorry

      euclid_sentence "3.9.11"
        "And the straight-lines $GK$ and $HL$ have no common (point) other than point $D$."
        (step11 : ∀ p : Point, p.onLine GK → p.onLine HL → p = d) := by sorry

      euclid_sentence "3.9.12"
        "Thus, point $D$ is the center of circle $ABC$."
        (step12 : d.isCentre ABC) := by sorry

      exact step12
  euclid_conclude_sentence "3.9.13"
    "Thus, if some point is taken inside a circle, and more than two equal straight-lines radiate from the point towards the (circumference of the) circle, (then) the point taken is the center of the circle. (Which is) the very thing it was required to show."

end Elements.Book3
