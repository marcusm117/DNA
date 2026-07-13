import SystemE
import Book1.Prop10.Main
import Book1Variants.Prop23
import Book3.Prop25.step1
import Book3.Prop25.step2
import Book3.Prop25.step3
import Book3.Prop25.step4
import Book3.Prop25.step5
import Book3.Prop25.step6
import Book3.Prop25.step7
import Book3.Prop25.step8
import Book3.Prop25.step9
import Book3.Prop25.step10
import Book3.Prop25.step11
import Book3.Prop25.step12
import Book3.Prop25.step13
import Book3.Prop25.step14
import Book3.Prop25.step15
import Book3.Prop25.step16
import Book3.Prop25.step17
import Book3.Prop25.step18
import Book3.Prop25.step19
import Book3.Prop25.step20
import Book3.Prop25.step21
import Book3.Prop25.step22
import Book3.Prop25.step23
import Book3.Prop25.hAGDB
import Book3.Prop25.hec
import Book3.Prop25.step9_assumption1
import Book3.Prop25.hda
import Book3.Prop25.haα₂
import Book3.Prop25.hbα₂
import Book3.Prop25.hcα₂
import Book3.Prop25.hAG3DB
import Book3.Prop25.hEb
import Book3.Prop25.hEc
import Book3.Prop25.haα₃
import Book3.Prop25.hbα₃
import Book3.Prop25.hcα₃
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

-- orchestrator-agreed: construction — a given segment (3 non-collinear points: chord AC + arc point b) → ∃ the completed
-- circle through all three. Clean, proof-faithful (proof exhibits center, [3.9] completes; final sentence = the ∃).
theorem proposition_25 : ∀ (a b c : Point) (AC : Line),
  a.onLine AC ∧ c.onLine AC ∧ a ≠ c ∧ ¬b.onLine AC ∧ |(a─b)| = |(c─b)| →
  ∃ (α : Circle), a.onCircle α ∧ b.onCircle α ∧ c.onCircle α :=
by
  euclid_intros
  euclid_intro_sentence "3.25.0"
    "For a given segment of a circle, to complete the circle, the very one of which it is a segment. Let $ABC$ be the given segment of a circle. So it is required to complete the circle for segment $ABC$, the very one of which it is a segment."

  euclid_apply (proposition_10 a c AC) as d
  euclid_apply (line_from_points d b) as DB
  euclid_apply (line_from_points a b) as AB

  euclid_sentence "3.25.1"
    "For let $AC$ be cut in half at (point) $D$ [Prop.~1.10],"
    (step1 : between a d c ∧ |(a─d)| = |(d─c)|) := by euclid_apply (helper_3_25_step1 a c d (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─c)|; assumption)))

  euclid_sentence "3.25.2"
    "and let $DB$ be drawn from point $D$, at right-angles to $AC$ [Prop.~1.11]."
    (step2 : ∠ a:d:b = ∟) := by euclid_apply (helper_3_25_step2 a b c d AC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show |(a─b)| = |(c─b)|; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─c)|; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)))

  euclid_sentence "3.25.3"
    "And let $AB$ be joined."
    (step3 : distinctPointsOnLine a b AB) := by euclid_apply (helper_3_25_step3 a b AC AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)))

  euclid_sentence "3.25.4"
    "Thus, angle $ABD$ is surely either greater than, equal to, or less than (angle) $BAD$."
    (step4 : ∠ a:b:d > ∠ b:a:d ∨ ∠ a:b:d = ∠ b:a:d ∨ ∠ a:b:d < ∠ b:a:d) := by euclid_apply (helper_3_25_step4 a b d)

  by_cases hgt : ∠ a:b:d > ∠ b:a:d
  ·
    euclid_sentence "3.25.5"
      "First of all, let it be greater."
      (step5 : ∠ a:b:d > ∠ b:a:d) := by euclid_apply (helper_3_25_step5 a b d (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))

    euclid_apply (proposition_23' a b b a d d AB AB DB) as g
    euclid_apply (line_from_points a g) as AG
    have hAGDB : AG.intersectsLine DB := by euclid_apply (helper_3_25_hAGDB a b c d g AC DB AB AG (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─c)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(c─b)|; assumption)))
    euclid_apply (intersection_lines AG DB) as e
    have hec : e ≠ c := by euclid_apply (helper_3_25_hec a b c d e AC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)))
    euclid_apply (line_from_points e c) as EC
    euclid_apply (circle_from_points e a) as α₁

    euclid_sentence "3.25.6"
      "And let (angle) $BAE$, equal to angle $ABD$, be constructed on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]."
      (step6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) := by euclid_apply (helper_3_25_step6 a b c d e g AC DB AB AG (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))

    euclid_sentence "3.25.7"
      "And let $DB$ be drawn through to $E$,"
      (step7 : e.onLine DB) := by euclid_apply (helper_3_25_step7 e DB (by euclid_assumption "" (show e.onLine DB; assumption)))

    euclid_sentence "3.25.8"
      "and let $EC$ be joined."
      (step8 : distinctPointsOnLine e c EC) := by euclid_apply (helper_3_25_step8 c e EC (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)))

    -- @assumption_gap
    have step9_assumption1 : ∠ a:b:e = ∠ b:a:e := by euclid_apply (helper_3_25_step9_assumption1 a b c d e g AC DB AB AG (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d ∧ e ≠ a; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))
    -- @assumption ("angle $ABE$ is equal to $BAE$", ∠ a:b:e = ∠ b:a:e)
    euclid_sentence "3.25.9"
      "Therefore, since angle $ABE$ is equal to $BAE$, the straight-line $EB$ is thus also equal to $EA$ [Prop.~1.6]."
      (step9 : |(e─b)| = |(e─a)|) := by euclid_apply (helper_3_25_step9 a b c d e g AC AG AB DB (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)) (by euclid_assumption "angle $ABE$ is equal to $BAE$" (show ∠ a:b:e = ∠ b:a:e; assumption)))

    -- @assumption_valid
    have step10_assumption1 : |(a─d)| = |(d─c)| := by assumption
    -- @assumption_valid
    have step10_assumption2 : |(d─e)| = |(d─e)| := by rfl
    -- @assumption ("$AD$ is equal to $DC$", |(a─d)| = |(d─c)|)
    -- @assumption ("$DE$ (is) common", |(d─e)| = |(d─e)|)
    euclid_sentence "3.25.10"
      "And since $AD$ is equal to $DC$, and $DE$ (is) common, the two (straight-lines) $AD$, $DE$ are equal to the two (straight-lines) $CD$, $DE$, respectively."
      (step10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|) := by euclid_apply (helper_3_25_step10 a c d e (by euclid_assumption "$AD$ is equal to $DC$" (show |(a─d)| = |(d─c)|; assumption)) (by euclid_assumption "$DE$ (is) common" (show |(d─e)| = |(d─e)|; assumption)))

    -- @assumption_valid
    have step11_assumption1 : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟ := by euclid_finish
    -- @assumption ("For each (is) a right-angle", ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    euclid_sentence "3.25.11"
      "And angle $ADE$ is equal to angle $CDE$. For each (is) a right-angle."
      (step11 : ∠ a:d:e = ∠ c:d:e) := by euclid_apply (helper_3_25_step11 a c d e (by euclid_assumption "For each (is) a right-angle" (show ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟; assumption)))

    euclid_sentence "3.25.12"
      "Thus, the base $AE$ is equal to the base $CE$ [Prop.~1.4]."
      (step12 : |(a─e)| = |(c─e)|) := by euclid_apply (helper_3_25_step12 a b c d e g AC DB AB AG EC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∠ c:d:e; assumption)))

    euclid_sentence "3.25.13"
      "But, $AE$ was shown (to be) equal to $BE$."
      (step13 : |(a─e)| = |(b─e)|) := by euclid_apply (helper_3_25_step13 a b e (by euclid_assumption "" (show |(e─b)| = |(e─a)|; assumption)))

    euclid_sentence "3.25.14"
      "Thus, $BE$ is also equal to $CE$."
      (step14 : |(b─e)| = |(c─e)|) := by euclid_apply (helper_3_25_step14 a b c e (by euclid_assumption "" (show |(a─e)| = |(c─e)|; assumption)) (by euclid_assumption "" (show |(a─e)| = |(b─e)|; assumption)))

    euclid_sentence "3.25.15"
      "Thus, the three (straight-lines) $AE$, $EB$, and $EC$ are equal to one another."
      (step15 : |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|) := by euclid_apply (helper_3_25_step15 a b c e (by euclid_assumption "" (show |(a─e)| = |(b─e)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(c─e)|; assumption)))

    euclid_sentence "3.25.16"
      "Thus, if a circle is drawn with center $E$, and radius one of $AE$, $EB$, or $EC$, it will also go through the remaining points (of the segment), and the (associated circle) will be completed [Prop.~3.9]."
      (step16 : e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁) := by euclid_apply (helper_3_25_step16 a b c e AC α₁ (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show e.isCentre α₁; assumption)) (by euclid_assumption "" (show a.onCircle α₁; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)|; assumption)))

    euclid_sentence "3.25.17"
      "Thus, a circle has been completed from the given segment of a circle."
      (step17 : a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁) := by euclid_apply (helper_3_25_step17 a b c e α₁ (by euclid_assumption "" (show e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁; assumption)))

    -- @assumption_valid
    have step18_assumption1 : e.opposingSides b AC := by euclid_finish
    -- @assumption ("because the center $E$ happens to lie outside it", e.opposingSides b AC)
    euclid_sentence "3.25.18"
      "And (it is) clear that the segment $ABC$ is less than a semi-circle, because the center $E$ happens to lie outside it."
      (step18 : e.opposingSides b AC) := by euclid_apply (helper_3_25_step18 b e AC (by euclid_assumption "because the center $E$ happens to lie outside it" (show e.opposingSides b AC; assumption)))

    exact ⟨α₁, step17⟩

  · by_cases heq : ∠ a:b:d = ∠ b:a:d
    ·
      -- @assumption_valid
      have step19_assumption1 : ∠ a:b:d = ∠ b:a:d := by assumption
      -- @assumption_valid
      have step19_assumption2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)| := by euclid_finish
      -- @assumption ("angle $ABD$ is equal to $BAD$", ∠ a:b:d = ∠ b:a:d)
      -- @assumption ("$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$", |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)
      euclid_sentence "3.25.19"
        "[And], similarly, even if angle $ABD$ is equal to $BAD$, (since) $AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$, the three (straight-lines) $DA$, $DB$, and $DC$ will be equal to one another."
        (step19 : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)|) := by euclid_apply (helper_3_25_step19 a b c d AC AB DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "angle $ABD$ is equal to $BAD$" (show ∠ a:b:d = ∠ b:a:d; assumption)) (by euclid_assumption "$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$" (show |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|; assumption)))

      -- D is the center; introduce circle α₂ with center D, point A on it
      have hda : d ≠ a := by euclid_apply (helper_3_25_hda a c d (by euclid_assumption "" (show between a d c; assumption)))
      euclid_apply (circle_from_points d a) as α₂

      euclid_sentence "3.25.20"
        "And point $D$ will be the center of the completed circle."
        (step20 : d.isCentre α₂) := by euclid_apply (helper_3_25_step20 d α₂ (by euclid_assumption "" (show d.isCentre α₂; assumption)))

      -- semicircle: center D lies between A and C on the chord (diameter)
      euclid_sentence "3.25.21"
        "And $ABC$ will manifestly be a semi-circle."
        (step21 : between a d c ∧ d.isCentre α₂) := by euclid_apply (helper_3_25_step21 a c d α₂ (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.isCentre α₂; assumption)))

      use α₂
      have haα₂ : a.onCircle α₂ := by euclid_apply (helper_3_25_haα₂ a α₂ (by euclid_assumption "" (show a.onCircle α₂; assumption)))
      have hbα₂ : b.onCircle α₂ := by euclid_apply (helper_3_25_hbα₂ a b d α₂ (by euclid_assumption "" (show d.isCentre α₂; assumption)) (by euclid_assumption "" (show a.onCircle α₂; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)))
      have hcα₂ : c.onCircle α₂ := by euclid_apply (helper_3_25_hcα₂ a b c d α₂ (by euclid_assumption "" (show d.isCentre α₂; assumption)) (by euclid_assumption "" (show a.onCircle α₂; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)) (by euclid_assumption "" (show |(d─b)| = |(d─c)|; assumption)))
      exact ⟨haα₂, hbα₂, hcα₂⟩

    -- Case 3: ∠ABD < ∠BAD
    ·
      euclid_apply (proposition_23' a b b a d d AB AB DB) as g3
      euclid_apply (line_from_points a g3) as AG3
      have hAG3DB : AG3.intersectsLine DB := by euclid_apply (helper_3_25_hAG3DB a b c d g3 AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ¬ ∠ a:b:d > ∠ b:a:d; assumption)) (by euclid_assumption "" (show ¬ ∠ a:b:d = ∠ b:a:d; assumption)))
      euclid_apply (intersection_lines AG3 DB) as e
      euclid_apply (circle_from_points e a) as α₃

      -- @assumption_valid
      have step22_assumption1 : ∠ a:b:d < ∠ b:a:d := by euclid_finish
      -- @assumption ("$ABD$ is less than $BAD$", ∠ a:b:d < ∠ b:a:d)
      euclid_sentence "3.25.22"
        "And if $ABD$ is less than $BAD$, and we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23], then the center will fall on $DB$, inside the segment $ABC$."
        (step22 : e.onLine DB ∧ e.sameSide b AC) := by euclid_apply (helper_3_25_step22 a b c d e g3 AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "$ABD$ is less than $BAD$" (show ∠ a:b:d < ∠ b:a:d; assumption)))

      -- greater than semicircle: center E inside the chord AC's arc side
      euclid_sentence "3.25.23"
        "And segment $ABC$ will manifestly be greater than a semi-circle."
        (step23 : b.sameSide e AC) := by euclid_apply (helper_3_25_step23 b e AC DB (by euclid_assumption "" (show e.onLine DB ∧ e.sameSide b AC; assumption)))

      have hEb : |(e─a)| = |(e─b)| := by euclid_apply (helper_3_25_hEb a b c d e g3 AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)) (by euclid_assumption "" (show e.onLine DB ∧ e.sameSide b AC; assumption)))
      have hEc : |(e─a)| = |(e─c)| := by euclid_apply (helper_3_25_hEc a b c d e AC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show |(a─d)| = |(d─c)|; assumption)) (by euclid_assumption "" (show e.onLine DB ∧ e.sameSide b AC; assumption)))
      use α₃
      have haα₃ : a.onCircle α₃ := by euclid_apply (helper_3_25_haα₃ a α₃ (by euclid_assumption "" (show a.onCircle α₃; assumption)))
      have hbα₃ : b.onCircle α₃ := by euclid_apply (helper_3_25_hbα₃ a b e α₃ (by euclid_assumption "" (show e.isCentre α₃; assumption)) (by euclid_assumption "" (show a.onCircle α₃; assumption)) (by euclid_assumption "" (show |(e─a)| = |(e─b)|; assumption)))
      have hcα₃ : c.onCircle α₃ := by euclid_apply (helper_3_25_hcα₃ a c e α₃ (by euclid_assumption "" (show e.isCentre α₃; assumption)) (by euclid_assumption "" (show a.onCircle α₃; assumption)) (by euclid_assumption "" (show |(e─a)| = |(e─c)|; assumption)))
      exact ⟨haα₃, hbα₃, hcα₃⟩

  euclid_conclude_sentence "3.25.24"
    "Thus, a circle has been completed from the given segment of a circle. (Which is) the very thing it was required to do."

end Elements.Book3
