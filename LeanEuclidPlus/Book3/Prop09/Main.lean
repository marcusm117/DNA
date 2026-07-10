import SystemE
import Book1.Prop10.Main
import Book3.Prop09.step1
import Book3.Prop09.step2
import Book3.Prop09.step3
import Book3.Prop09.step4
import Book3.Prop09.step5
import Book3.Prop09.step6
import Book3.Prop09.step7
import Book3.Prop09.step8
import Book3.Prop09.step9
import Book3.Prop09.step10
import Book3.Prop09.step11
import Book3.Prop09.step12
import Book3.Prop09.hcentre
import Book3.Prop09.step9_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

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
             between a e b ∧ |(a─e)| = |(e─b)| ∧ between b f c ∧ |(b─f)| = |(f─c)|) := by euclid_apply (helper_3_9_step1 a b c e f AB BC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─b)|; assumption)) (by euclid_assumption "" (show between b f c; assumption)) (by euclid_assumption "" (show |(b─f)| = |(f─c)|; assumption)))

  -- @euclid_gap (generic-position): Euclid draws AB, BC as generic chords and reads E, F ≠ D off
  -- the figure. When a chord is a DIAMETER its midpoint equals the centre = D (E = D or F = D), and
  -- the perpendicular bisector GK / HL degenerates. Those two cases are split off here — D is then
  -- directly the centre (equidistant from A, B, C). At most one occurs (AB, BC share B; two diameters
  -- would meet at the centre = B, impossible as B is on the circle). Generic branch = Euclid's argument.
  by_cases h_ed : e = d
  ·
    -- @euclid_gap: AB is a diameter ⟹ E = D = centre; D is directly the centre (equidistant A,B,C)
    have hcentre : d.isCentre ABC := by euclid_apply (helper_3_9_hcentre ABC a b c d e f AB BC (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)) (by euclid_assumption "" (show |(d─b)| = |(d─c)|; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧ between b f c ∧ |(b─f)| = |(f─c)|; assumption)))
    exact hcentre
  · by_cases h_fd : f = d
    ·
      -- @euclid_gap: BC is a diameter ⟹ F = D = centre; D is directly the centre
      have hcentre : d.isCentre ABC := by euclid_apply (helper_3_9_hcentre ABC a b c d e f AB BC (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)) (by euclid_assumption "" (show |(d─b)| = |(d─c)|; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧ between b f c ∧ |(b─f)| = |(f─c)|; assumption)))
      exact hcentre
    · have he_ne_d : e ≠ d := h_ed
      have hf_ne_d : f ≠ d := h_fd
      euclid_apply (line_from_points e d) as GK
      euclid_apply (line_from_points f d) as HL
      euclid_apply (intersection_circle_line_extending_points ABC GK d e) as g
      euclid_apply (intersection_circle_line_extending_points ABC GK d g) as k
      euclid_apply (intersection_circle_line_extending_points ABC HL d f) as h
      euclid_apply (intersection_circle_line_extending_points ABC HL d h) as l
      euclid_sentence "3.9.2"
        "And $ED$ and $FD$ being joined, let them be drawn through to points $G$, $K$, $H$, and $L$."
        (step2 :
          -- ED joined (E, D on line GK), produced through to G, K on the circle:
          (e.onLine GK ∧ d.onLine GK) ∧
          (g.onCircle ABC ∧ g.onLine GK) ∧ (k.onCircle ABC ∧ k.onLine GK) ∧
          -- FD joined (F, D on line HL), produced through to H, L on the circle:
          (f.onLine HL ∧ d.onLine HL) ∧
          (h.onCircle ABC ∧ h.onLine HL) ∧ (l.onCircle ABC ∧ l.onLine HL)) := by euclid_apply (helper_3_9_step2 ABC d e f g h k l GK HL (by euclid_assumption "" (show e.onLine GK; assumption)) (by euclid_assumption "" (show d.onLine GK; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onLine GK; assumption)) (by euclid_assumption "" (show k.onCircle ABC; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show f.onLine HL; assumption)) (by euclid_assumption "" (show d.onLine HL; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show h.onLine HL; assumption)) (by euclid_assumption "" (show l.onCircle ABC; assumption)) (by euclid_assumption "" (show l.onLine HL; assumption)))

      -- @assumption_valid
      have step3_assumption1 : |(a─e)| = |(e─b)| := by assumption
      -- @assumption_valid
      have step3_assumption2 : |(e─d)| = |(e─d)| := by rfl
      -- @assumption ("$AE$ is equal to $EB$", |(a─e)| = |(e─b)|)
      -- @assumption ("$ED$ (is) common", |(e─d)| = |(e─d)|)
      euclid_sentence "3.9.3"
        "Therefore, since $AE$ is equal to $EB$, and $ED$ (is) common, the two (straight-lines) $AE$, $ED$ are equal to the two (straight-lines) $BE$, $ED$ (respectively)."
        (step3 : |(a─e)| = |(b─e)| ∧ |(e─d)| = |(e─d)|) := by euclid_apply (helper_3_9_step3 a b d e (by euclid_assumption "$AE$ is equal to $EB$" (show |(a─e)| = |(e─b)|; assumption)) (by euclid_assumption "$ED$ (is) common" (show |(e─d)| = |(e─d)|; assumption)))

      euclid_sentence "3.9.4"
        "And the base $DA$ (is) equal to the base $DB$."
        (step4 : |(d─a)| = |(d─b)|) := by euclid_apply (helper_3_9_step4 a b d (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)))

      euclid_sentence "3.9.5"
        "Thus, angle $AED$ is equal to angle $BED$ [Prop.~1.8]."
        (step5 : ∠ a:e:d = ∠ b:e:d) := by euclid_apply (helper_3_9_step5 ABC a b d e AB GK (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine GK; assumption)) (by euclid_assumption "" (show d.onLine GK; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show e ≠ d; assumption)) (by euclid_assumption "" (show |(a─e)| = |(b─e)| ∧ |(e─d)| = |(e─d)|; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)))

      euclid_sentence "3.9.6"
        "Thus, angles $AED$ and $BED$ (are) each right-angles [Def.~1.10]."
        (step6 : ∠ a:e:d = ∟ ∧ ∠ b:e:d = ∟) := by euclid_apply (helper_3_9_step6 ABC a b d e g AB GK (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine GK; assumption)) (by euclid_assumption "" (show d.onLine GK; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show e ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(a─e)| = |(b─e)| ∧ |(e─d)| = |(e─d)|; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)) (by euclid_assumption "" (show ∠ a:e:d = ∠ b:e:d; assumption)) (by euclid_assumption "" (show between g d e; assumption)))

      euclid_sentence "3.9.7"
        "Thus, $GK$ cuts $AB$ in half,"
        (step7 : e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)|) := by euclid_apply (helper_3_9_step7 a b e GK (by euclid_assumption "" (show e.onLine GK; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─b)|; assumption)))

      euclid_sentence "3.9.8"
        "and at right-angles."
        (step8 : ∠ a:e:d = ∟) := by euclid_apply (helper_3_9_step8 a b d e (by euclid_assumption "" (show ∠ a:e:d = ∟ ∧ ∠ b:e:d = ∟; assumption)))

      -- @assumption_gap
      have step9_assumption1 : e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧ ∠ a:e:d = ∟ → ∀ o : Point, o.isCentre ABC → o.onLine GK := by euclid_apply (helper_3_9_step9_assumption1 ABC a b d e AB GK (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine GK; assumption)) (by euclid_assumption "" (show d.onLine GK; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show e ≠ d; assumption)) (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)))
      -- @assumption ("if some straight-line in a circle cuts some (other) straight-line in half, and at right-angles, (then) the center of the circle is on the former (straight-line)", e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧ ∠ a:e:d = ∟ → ∀ o : Point, o.isCentre ABC → o.onLine GK)
      euclid_sentence "3.9.9"
        "And since, if some straight-line in a circle cuts some (other) straight-line in half, and at right-angles, (then) the center of the circle is on the former (straight-line) [Prop.~3.1~corr.], the center of the circle is thus on $GK$."
        (step9 : ∀ o : Point, o.isCentre ABC → o.onLine GK) := by euclid_apply (helper_3_9_step9 ABC a b d e AB GK (by euclid_assumption "" (show e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)|; assumption)) (by euclid_assumption "" (show ∠ a:e:d = ∟; assumption)) (by euclid_assumption "if some straight-line in a circle cuts some (other) straight-line in half, and at right-angles, (then) the center of the circle is on the former (straight-line)" (show e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧ ∠ a:e:d = ∟ → ∀ o : Point, o.isCentre ABC → o.onLine GK; assumption)))

      euclid_sentence "3.9.10"
        "So, for the same (reasons), the center of circle $ABC$ is also on $HL$."
        (step10 : ∀ o : Point, o.isCentre ABC → o.onLine HL) := by euclid_apply (helper_3_9_step10 ABC b c d f BC HL (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show f.onLine HL; assumption)) (by euclid_assumption "" (show d.onLine HL; assumption)) (by euclid_assumption "" (show between b f c; assumption)) (by euclid_assumption "" (show |(b─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show |(d─b)| = |(d─c)|; assumption)) (by euclid_assumption "" (show f ≠ d; assumption)))

      euclid_sentence "3.9.11"
        "And the straight-lines $GK$ and $HL$ have no common (point) other than point $D$."
        (step11 : ∀ p : Point, p.onLine GK → p.onLine HL → p = d) := by euclid_apply (helper_3_9_step11 ABC a b c d e f AB BC GK HL (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show d.insideCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine GK; assumption)) (by euclid_assumption "" (show d.onLine GK; assumption)) (by euclid_assumption "" (show f.onLine HL; assumption)) (by euclid_assumption "" (show d.onLine HL; assumption)) (by euclid_assumption "" (show between a e b; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─b)|; assumption)) (by euclid_assumption "" (show between b f c; assumption)) (by euclid_assumption "" (show |(b─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)) (by euclid_assumption "" (show |(d─b)| = |(d─c)|; assumption)) (by euclid_assumption "" (show ∠ a:e:d = ∟; assumption)) (by euclid_assumption "" (show e ≠ d; assumption)) (by euclid_assumption "" (show f ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)))

      euclid_sentence "3.9.12"
        "Thus, point $D$ is the center of circle $ABC$."
        (step12 : d.isCentre ABC) := by euclid_apply (helper_3_9_step12 ABC d GK HL (by euclid_assumption "" (show ∀ o : Point, o.isCentre ABC → o.onLine GK; assumption)) (by euclid_assumption "" (show ∀ o : Point, o.isCentre ABC → o.onLine HL; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine GK → p.onLine HL → p = d; assumption)))

      exact step12
  euclid_conclude_sentence "3.9.13"
    "Thus, if some point is taken inside a circle, and more than two equal straight-lines radiate from the point towards the (circumference of the) circle, (then) the point taken is the center of the circle. (Which is) the very thing it was required to show."

end Elements.Book3
