import SystemE
import Book1.Prop10.Main
import Book1.Prop11.Main
import Book1.Prop23.Main
import Book3.Prop16.Main
import Book3.Prop32.Main
import Mathlib.Tactic.Linarith
import Book3.Prop33.step1
import Book3.Prop33.step2
import Book3.Prop33.step3
import Book3.Prop33.step4
import Book3.Prop33.step5
import Book3.Prop33.step6
import Book3.Prop33.step7
import Book3.Prop33.step8
import Book3.Prop33.step9
import Book3.Prop33.step10
import Book3.Prop33.step11
import Book3.Prop33.step12
import Book3.Prop33.step13
import Book3.Prop33.step14
import Book3.Prop33.step15
import Book3.Prop33.step16
import Book3.Prop33.step17
import Book3.Prop33.step19
import Book3.Prop33.step20
import Book3.Prop33.step21
import Book3.Prop33.step22
import Book3.Prop33.step23
import Book3.Prop33.step24
import Book3.Prop33.step25
import Book3.Prop33.step26
import Book3.Prop33.step28
import Book3.Prop33.step29
import Book3.Prop33.step30
import Book3.Prop33.step31
import Book3.Prop33.step32
import Book3.Prop33.step33
import Book3.Prop33.step34
import Book3.Prop33.step35
import Book3.Prop33.step36
import Book3.Prop33.step37
import Book3.Prop33.step38
import Book3.Prop33.step39
import Book3.Prop33.step40
import Book3.Prop33.step41
import Book3.Prop33.step42
import Book3.Prop33.hFG_int_AE
import Book3.Prop33.hga
import Book3.Prop33.hgb
import Book3.Prop33.hb_circ
import Book3.Prop33.heb
import Book3.Prop33.hfa
import Book3.Prop33.hb_circ_2
import Book3.Prop33.he_off
import Book3.Prop33.step23_assumption1
import Book3.Prop33.hFGcirc
import Book3.Prop33.hh_straddle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem proposition_33 : ∀ (a b c₁ c c₂ : Point),
  a ≠ b →
  c₁ ≠ c → c ≠ c₂ →
  0 < ∠ c₁:c:c₂ → ∠ c₁:c:c₂ < ∟ + ∟ →
  ∃ (α : Circle) (e : Point), a.onCircle α ∧ b.onCircle α ∧ e.onCircle α ∧ ∠ a:e:b = ∠ c₁:c:c₂ :=
by
  euclid_intros
  euclid_intro_sentence "3.33.0"
    "To draw a segment of a circle, accepting an angle equal to a given rectilinear angle, on a given straight-line. Let $AB$ be the given straight-line, and $C$ the given rectilinear angle. So it is required to draw a segment of a circle, accepting an angle equal to $C$, on the given straight-line $AB$. So the [angle] $C$ is surely either acute, a right-angle, or obtuse. First of all, let it be acute."

  rcases lt_trichotomy (∠ c₁:c:c₂) ∟ with hacute | hright | hobtuse

  -- ── CASE 1 : ∠ c₁:c:c₂ < ∟  (acute) ─────────────────────────────────────────
  ·
    have hnrt : ∠ c₁:c:c₂ ≠ ∟ := ne_of_lt hacute
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = angle C at A on AB [Prop 1.23]
    euclid_apply (line_from_points c c₁) as CC1
    euclid_apply (line_from_points c c₂) as CC2
    euclid_apply (proposition_23 a b c c₁ c₂ AB CC1 CC2) as d
    euclid_apply (line_from_points a d) as AD
    -- AE at right-angles to DA at A [Prop 1.11]: extend AD past A, erect ⊥ at A (direction e0)
    euclid_apply (extend_point AD d a) as d0
    euclid_apply (proposition_11 d d0 a AD) as e0
    euclid_apply (line_from_points a e0) as AE
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    -- FG at right-angles to AB at F [Prop 1.11]; G = FG ∩ AE (centre of the circle)
    euclid_apply (proposition_11 a b f AB) as g0
    euclid_apply (line_from_points f g0) as FG
    have hFG_int_AE : FG.intersectsLine AE := by euclid_apply (helper_3_33_hFG_int_AE a b c₁ c c₂ d e0 f g0 AB AD AE FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ¬g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
    euclid_apply (intersection_lines FG AE) as g
    have hga : g ≠ a := by euclid_apply (helper_3_33_hga a b f g g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))
    euclid_apply (circle_from_points g a) as α
    -- E = the far end of diameter AE (on the circle, since centre G lies on AE)
    euclid_apply (intersection_circle_line_extending_points α AE g a) as e
    have hgb : g ≠ b := by euclid_apply (helper_3_33_hgb a b f g g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))
    euclid_apply (line_from_points g b) as GB
    -- B also lies on this circle (proved via AG = BG from SAS)
    have hb_circ : b.onCircle α := by euclid_apply (helper_3_33_hb_circ a b c₁ c c₂ d e0 f g g0 AB AD AE FG GB α (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)))
    -- EB joined
    have heb : e ≠ b := by euclid_apply (helper_3_33_heb a b c₁ c c₂ d e0 e AB AD AE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)))
    euclid_apply (line_from_points e b) as EB

    euclid_sentence "3.33.1"
      "And, as in the first diagram (from the left), let (angle) $BAD$, equal to angle $C$, be constructed on the straight-line $AB$, at the point A (on it) [Prop.~1.23]."
      (step1 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step1 a b d c₁ c c₂ (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.2"
      "Thus, $BAD$ is also acute."
      (step2 : ∠ b:a:d < ∟) := by euclid_apply (helper_3_33_step2 a b d c₁ c c₂ (by euclid_assumption "" (show ∠ b:a:d = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟; assumption)))

    euclid_sentence "3.33.3"
      "Let $AE$ be drawn, at right-angles to $DA$ [Prop.~1.11]."
      (step3 : ∠ d:a:e = ∟) := by euclid_apply (helper_3_33_step3 a d e e0 g AD AE (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show between e g a; assumption)))

    euclid_sentence "3.33.4"
      "And let $AB$ be cut in half at $F$ [Prop.~1.10]."
      (step4 : between a f b ∧ |(a─f)| = |(f─b)|) := by euclid_apply (helper_3_33_step4 a b f (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)))

    euclid_sentence "3.33.5"
      "And let $FG$ be drawn from point $F$, at right-angles to $AB$ [Prop.~1.11]."
      (step5 : ∠ a:f:g = ∟) := by euclid_apply (helper_3_33_step5 a b c₁ c c₂ d e0 f g g0 AB AD AE FG (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))

    euclid_sentence "3.33.6"
      "And let $GB$ be joined."
      (step6 : distinctPointsOnLine g b GB) := by euclid_apply (helper_3_33_step6 g b GB (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)))

    -- @assumption_valid
    have step7_assumption1 : |(a─f)| = |(f─b)| := by assumption
    -- @assumption_valid
    have step7_assumption2 : |(f─g)| = |(f─g)| := by rfl
    -- @assumption ("$AF$ is equal to $FB$", |(a─f)| = |(f─b)|)
    -- @assumption ("$FG$ (is) common", |(f─g)| = |(f─g)|)
    euclid_sentence "3.33.7"
      "And since $AF$ is equal to $FB$, and $FG$ (is) common, the two (straight-lines) $AF$, $FG$ are equal to the two (straight-lines) $BF$, $FG$ (respectively)."
      (step7 : |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)|) := by euclid_apply (helper_3_33_step7 a b f g (by euclid_assumption "$AF$ is equal to $FB$" (show |(a─f)| = |(f─b)|; assumption)) (by euclid_assumption "$FG$ (is) common" (show |(f─g)| = |(f─g)|; assumption)))

    euclid_sentence "3.33.8"
      "And angle $AFG$ (is) equal to [angle] $BFG$."
      (step8 : ∠ a:f:g = ∠ b:f:g) := by euclid_apply (helper_3_33_step8 a b c₁ c c₂ d e0 f g AB AD AE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ∠ a:f:g = ∟; assumption)))

    euclid_sentence "3.33.9"
      "Thus, the base $AG$ is equal to the base $BG$ [Prop.~1.4]."
      (step9 : |(a─g)| = |(b─g)|) := by euclid_apply (helper_3_33_step9 a b c₁ c c₂ d e0 f g g0 AB AD AE FG GB (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)))

    euclid_sentence "3.33.10"
      "Thus, the circle drawn with center $G$, and radius $GA$, will also go through $B$ (as well as $A$)."
      (step10 : a.onCircle α ∧ b.onCircle α) := by euclid_apply (helper_3_33_step10 a b α (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)))

    euclid_sentence "3.33.11"
      "Let it be drawn, and let it be (denoted) $ABE$."
      (step11 : g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ e.onCircle α) := by euclid_apply (helper_3_33_step11 a b e g α (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)))

    euclid_sentence "3.33.12"
      "And let $EB$ be joined."
      (step12 : distinctPointsOnLine e b EB) := by euclid_apply (helper_3_33_step12 e b EB (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))

    -- @assumption_valid
    have step13_assumption1 : ∠ d:a:e = ∟ := by assumption
    -- @assumption ("$AD$ is at the extremity of diameter $AE$, (namely, point) $A$, at right-angles to $AE$", ∠ d:a:e = ∟)
    euclid_sentence "3.33.13"
      "Therefore, since $AD$ is at the extremity of diameter $AE$, (namely, point) $A$, at right-angles to $AE$, the (straight-line) $AD$ thus touches the circle $ABE$ [Prop.~3.16~corr.]."
      (step13 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by euclid_apply (helper_3_33_step13 a d e g AD α (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show between e g a; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "$AD$ is at the extremity of diameter $AE$, (namely, point) $A$, at right-angles to $AE$" (show ∠ d:a:e = ∟; assumption)))

    -- @assumption_valid
    have step14_assumption1 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α := by assumption
    -- @assumption_valid
    have step14_assumption2 : a.onLine AB ∧ b.onLine AB ∧ b.onCircle α := by euclid_finish
    -- @assumption ("some straight-line $AD$ touches the circle $ABE$", (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α)
    -- @assumption ("some (other) straight-line $AB$ has been drawn across from the point of contact $A$ into circle $ABE$", a.onLine AB ∧ b.onLine AB ∧ b.onCircle α)
    euclid_sentence "3.33.14"
      "Therefore, since some straight-line $AD$ touches the circle $ABE$, and some (other) straight-line $AB$ has been drawn across from the point of contact $A$ into circle $ABE$, angle $DAB$ is thus equal to the angle $AEB$ in the alternate segment of the circle [Prop.~3.32]."
      (step14 : ∠ d:a:b = ∠ a:e:b) := by euclid_apply (helper_3_33_step14 a b d d0 e f g g0 AB AD AE FG α (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show between e g a; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:d < ∟; assumption)) (by euclid_assumption "some straight-line $AD$ touches the circle $ABE$" (show (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α; assumption)) (by euclid_assumption "some (other) straight-line $AB$ has been drawn across from the point of contact $A$ into circle $ABE$" (show a.onLine AB ∧ b.onLine AB ∧ b.onCircle α; assumption)))

    euclid_sentence "3.33.15"
      "But, $DAB$ is equal to $C$."
      (step15 : ∠ d:a:b = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step15 a b d c₁ c c₂ (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.16"
      "Thus, angle $C$ is also equal to $AEB$."
      (step16 : ∠ c₁:c:c₂ = ∠ a:e:b) := by euclid_apply (helper_3_33_step16 a b d e c₁ c c₂ (by euclid_assumption "" (show ∠ d:a:b = ∠ a:e:b; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.17"
      "Thus, a segment $AEB$ of a circle, accepting the angle $AEB$ (which is) equal to the given (angle) $C$, has been drawn on the given straight-line $AB$."
      (step17 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step17 a b e c₁ c c₂ α (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ = ∠ a:e:b; assumption)))

    exact step17

  -- ── CASE 2 : ∠ c₁:c:c₂ = ∟  (right angle) ─────────────────────────────────────
  ·
    euclid_wts "3.33.18"
      "And so let $C$ be a right-angle. And let it again be necessary to draw a segment of a circle on $AB$, accepting an angle equal to the right-[angle] $C$."

    -- Construction witnesses
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = right-angle C at A on AB [Prop 1.23]
    euclid_apply (line_from_points c c₁) as CC1
    euclid_apply (line_from_points c c₂) as CC2
    euclid_apply (proposition_23 a b c c₁ c₂ AB CC1 CC2) as d
    euclid_apply (line_from_points a d) as AD
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    have hfa : f ≠ a := by euclid_apply (helper_3_33_hfa a b f (by euclid_assumption "" (show between a f b; assumption)))
    -- Circle AEB with center F, radius FA (= FB since F is midpoint)
    euclid_apply (circle_from_points f a) as α
    have hb_circ_2 : b.onCircle α := by euclid_apply (helper_3_33_hb_circ_2 a b f α (by euclid_assumption "" (show f.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)))
    -- E: a point on circle α not on AB (perpendicular to AB at centre F meets the circle)
    euclid_apply (proposition_11 a b f AB) as g0
    euclid_apply (line_from_points f g0) as FG
    euclid_apply (intersection_circle_line_extending_points α FG f g0) as e
    have he_off : ¬ e.onLine AB := by euclid_apply (helper_3_33_he_off a b e f g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine FG; assumption)) (by euclid_assumption "" (show between e f g0; assumption)))

    euclid_sentence "3.33.19"
      "Let the (angle) $BAD$ [again] be constructed, equal to the right-angle $C$ [Prop.~1.23], as in the second diagram (from the left)."
      (step19 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step19 a b d c₁ c c₂ (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.20"
      "And let $AB$ be cut in half at $F$ [Prop.~1.10]."
      (step20 : between a f b ∧ |(a─f)| = |(f─b)|) := by euclid_apply (helper_3_33_step20 a b f (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)))

    euclid_sentence "3.33.21"
      "And let the circle $AEB$ be drawn with center $F$, and radius either $FA$ or $FB$."
      (step21 : f.isCentre α ∧ a.onCircle α ∧ b.onCircle α) := by euclid_apply (helper_3_33_step21 a b f α (by euclid_assumption "" (show f.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)))

    -- @assumption_valid
    have step22_assumption1 : ∠ b:a:d = ∟ := by linarith
    -- @assumption ("the angle at $A$ being a right-angle", ∠ b:a:d = ∟)
    euclid_sentence "3.33.22"
      "Thus, the straight-line $AD$ touches the circle $ABE$, on account of the angle at $A$ being a right-angle [Prop.~3.16 corr.]."
      (step22 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by euclid_apply (helper_3_33_step22 a b d f AD α (by euclid_assumption "" (show f.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "the angle at $A$ being a right-angle" (show ∠ b:a:d = ∟; assumption)))

    -- @suppress_deps_check "III.31 is skipped (its horn-angle segment addendum is not formalizable in System E); the semicircle right angle is re-derived in step23_assumption1 from I.5 + I.32 (as in Book3/Prop32/step6)."
    -- @assumption_gap
    have step23_assumption1 : ∠ a:e:b = ∟ := by euclid_apply (helper_3_33_step23_assumption1 a b e f α AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show f.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ¬ e.onLine AB; assumption)))
    -- @assumption ("(the latter angle), being in a semi-circle, is also a right-angle", ∠ a:e:b = ∟)
    euclid_sentence "3.33.23"
      "And angle $BAD$ is equal to the angle in segment $AEB$. For (the latter angle), being in a semi-circle, is also a right-angle [Prop.~3.31]."
      (step23 : ∠ b:a:d = ∠ a:e:b) := by euclid_apply (helper_3_33_step23 a b d e (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "(the latter angle), being in a semi-circle, is also a right-angle" (show ∠ a:e:b = ∟; assumption)))

    euclid_sentence "3.33.24"
      "But, $BAD$ is also equal to $C$."
      (step24 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step24 a b d c₁ c c₂ (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.25"
      "Thus, the (angle) in (segment) $AEB$ is also equal to $C$."
      (step25 : ∠ a:e:b = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step25 a b d e c₁ c c₂ (by euclid_assumption "" (show ∠ b:a:d = ∠ a:e:b; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.26"
      "Thus, a segment $AEB$ of a circle, accepting an angle equal to $C$, has again been drawn on $AB$."
      (step26 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step26 a b e c₁ c c₂ α (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show ∠ a:e:b = ∠ c₁:c:c₂; assumption)))

    exact step26

  -- ── CASE 3 : ∟ < ∠ c₁:c:c₂  (obtuse) ─────────────────────────────────────────
  ·
    have hnrt : ∠ c₁:c:c₂ ≠ ∟ := (ne_of_lt hobtuse).symm
    euclid_wts "3.33.27"
      "And so let (angle) $C$ be obtuse."

    -- Construction witnesses
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = obtuse angle C at A on AB [Prop 1.23]
    euclid_apply (line_from_points c c₁) as CC1
    euclid_apply (line_from_points c c₂) as CC2
    euclid_apply (proposition_23 a b c c₁ c₂ AB CC1 CC2) as d
    euclid_apply (line_from_points a d) as AD
    -- AE at right-angles to AD at A [Prop 1.11]: extend AD past A, erect ⊥ at A (direction e0)
    euclid_apply (extend_point AD d a) as d0
    euclid_apply (proposition_11 d d0 a AD) as e0
    euclid_apply (line_from_points a e0) as AE
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    -- FG at right-angles to AB at F [Prop 1.11]; G = FG ∩ AE (centre of the circle)
    euclid_apply (proposition_11 a b f AB) as g0
    euclid_apply (line_from_points f g0) as FG
    have hFG_int_AE : FG.intersectsLine AE := by euclid_apply (helper_3_33_hFG_int_AE a b c₁ c c₂ d e0 f g0 AB AD AE FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ¬g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)))
    euclid_apply (intersection_lines FG AE) as g
    have hga : g ≠ a := by euclid_apply (helper_3_33_hga a b f g g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))
    have hgb : g ≠ b := by euclid_apply (helper_3_33_hgb a b f g g0 AB FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))
    euclid_apply (line_from_points g b) as GB
    -- Circle with center G, radius GA
    euclid_apply (circle_from_points g a) as α
    have hb_circ : b.onCircle α := by euclid_apply (helper_3_33_hb_circ a b c₁ c c₂ d e0 f g g0 AB AD AE FG GB α (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)))
    -- H: a point on the circle in the alternate segment AHB (opposite side of AB from D). FG (through
    -- centre g) is a diameter, so it meets α at two points straddling AB at the interior point f; pick
    -- the one on the far side of AB from d.
    have hFGcirc : FG.intersectsCircle α := by euclid_apply (helper_3_33_hFGcirc g FG α (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))
    euclid_apply (intersections_circle_line α FG) as (h1, h2)
    have hh_straddle : h1.opposingSides h2 AB := by euclid_apply (helper_3_33_hh_straddle a b f g g0 h1 h2 AB FG α (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show h1.onCircle α; assumption)) (by euclid_assumption "" (show h2.onCircle α; assumption)) (by euclid_assumption "" (show h1.onLine FG; assumption)) (by euclid_assumption "" (show h2.onLine FG; assumption)) (by euclid_assumption "" (show h1 ≠ h2; assumption)))
    -- h is the inscribed point opposite d (alternate segment); h' the other FG∩α point, opposite d0.
    have hh_ex : ∃ hh hh' : Point, hh.onCircle α ∧ hh.opposingSides d AB ∧
        hh'.onCircle α ∧ hh'.opposingSides d0 AB := by
      by_cases hd1 : h1.opposingSides d AB
      · exact ⟨h1, h2, by euclid_finish, hd1, by euclid_finish, by euclid_finish⟩
      · exact ⟨h2, h1, by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish⟩
    obtain ⟨h, h', hh_circ, hh_side, hh'_circ, hh'_side⟩ := hh_ex

    euclid_sentence "3.33.28"
      "And let (angle) $BAD$, equal to ($C$), be constructed on the straight-line $AB$, at the point $A$ (on it) [Prop.~1.23], as in the third diagram (from the left)."
      (step28 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step28 a b d c₁ c c₂ (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.29"
      "And let $AE$ be drawn, at right-angles to $AD$ [Prop.~1.11]."
      (step29 : ∠ d:a:e0 = ∟) := by euclid_apply (helper_3_33_step29 a d e0 (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)))

    euclid_sentence "3.33.30"
      "And let $AB$ again be cut in half at $F$ [Prop.~1.10]."
      (step30 : between a f b ∧ |(a─f)| = |(f─b)|) := by euclid_apply (helper_3_33_step30 a b f (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)))

    euclid_sentence "3.33.31"
      "And let $FG$ be drawn, at right-angles to $AB$ [Prop.~1.10]."
      (step31 : ∠ a:f:g = ∟) := by euclid_apply (helper_3_33_step31 a b c₁ c c₂ d e0 f g g0 AB AD AE FG (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))

    euclid_sentence "3.33.32"
      "And let $GB$ be joined."
      (step32 : distinctPointsOnLine g b GB) := by euclid_apply (helper_3_33_step32 g b GB (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)))

    -- @assumption_valid
    have step33_assumption1 : |(a─f)| = |(f─b)| := by assumption
    -- @assumption_valid
    have step33_assumption2 : |(f─g)| = |(f─g)| := by rfl
    -- @assumption ("$AF$ is equal to $FB$", |(a─f)| = |(f─b)|)
    -- @assumption ("$FG$ (is) common", |(f─g)| = |(f─g)|)
    euclid_sentence "3.33.33"
      "And again, since $AF$ is equal to $FB$, and $FG$ (is) common, the two (straight-lines) $AF$, $FG$ are equal to the two (straight-lines) $BF$, $FG$ (respectively)."
      (step33 : |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)|) := by euclid_apply (helper_3_33_step33 a b f g (by euclid_assumption "$AF$ is equal to $FB$" (show |(a─f)| = |(f─b)|; assumption)) (by euclid_assumption "$FG$ (is) common" (show |(f─g)| = |(f─g)|; assumption)))

    euclid_sentence "3.33.34"
      "And angle $AFG$ (is) equal to angle $BFG$."
      (step34 : ∠ a:f:g = ∠ b:f:g) := by euclid_apply (helper_3_33_step34 a b c₁ c c₂ d e0 f g AB AD AE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ∠ a:f:g = ∟; assumption)))

    euclid_sentence "3.33.35"
      "Thus, the base $AG$ is equal to the base $BG$ [Prop.~1.4]."
      (step35 : |(a─g)| = |(b─g)|) := by euclid_apply (helper_3_33_step35 a b c₁ c c₂ d e0 f g g0 AB AD AE FG GB (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c₁ ≠ c; assumption)) (by euclid_assumption "" (show c ≠ c₂; assumption)) (by euclid_assumption "" (show 0 < ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ < ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ c₁:c:c₂ ≠ ∟; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:g0 = ∟; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g ≠ b; assumption)))

    euclid_sentence "3.33.36"
      "Thus, a circle of center $G$, and radius $GA$, being drawn, will also go through $B$ (as well as $A$)."
      (step36 : a.onCircle α ∧ b.onCircle α) := by euclid_apply (helper_3_33_step36 a b α (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)))

    euclid_sentence "3.33.37"
      "Let it go like $AEB$ (in the third diagram from the left)."
      (step37 : g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ h.onCircle α) := by euclid_apply (helper_3_33_step37 a b g h α (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show h.onCircle α; assumption)))

    -- @assumption_valid
    have step38_assumption1 : ∠ d:a:e0 = ∟ := by assumption
    -- @assumption ("$AD$ is at right-angles to the diameter $AE$, at its extremity", ∠ d:a:e0 = ∟)
    euclid_sentence "3.33.38"
      "And since $AD$ is at right-angles to the diameter $AE$, at its extremity, $AD$ thus touches circle $AEB$ [Prop.~3.16~corr.]."
      (step38 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by euclid_apply (helper_3_33_step38 a d e0 g AD AE α (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show g.onLine AE; assumption)) (by euclid_assumption "$AD$ is at right-angles to the diameter $AE$, at its extremity" (show ∠ d:a:e0 = ∟; assumption)))

    -- @assumption_valid
    have step39_assumption1 : a.onLine AB ∧ b.onLine AB ∧ b.onCircle α := by euclid_finish
    -- @assumption ("$AB$ has been drawn across (the circle) from the point of contact $A$", a.onLine AB ∧ b.onLine AB ∧ b.onCircle α)
    euclid_sentence "3.33.39"
      "And $AB$ has been drawn across (the circle) from the point of contact $A$. Thus, angle $BAD$ is equal to the angle constructed in the alternate segment $AHB$ of the circle [Prop.~3.32]."
      (step39 : ∠ b:a:d = ∠ a:h:b) := by euclid_apply (helper_3_33_step39 a b d d0 h h' AB AD α (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show h.onCircle α; assumption)) (by euclid_assumption "" (show h.opposingSides d AB; assumption)) (by euclid_assumption "" (show h'.onCircle α; assumption)) (by euclid_assumption "" (show h'.opposingSides d0 AB; assumption)) (by euclid_assumption "" (show (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α; assumption)) (by euclid_assumption "$AB$ has been drawn across (the circle) from the point of contact $A$" (show a.onLine AB ∧ b.onLine AB ∧ b.onCircle α; assumption)))

    euclid_sentence "3.33.40"
      "But, angle $BAD$ is equal to $C$."
      (step40 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step40 a b d c₁ c c₂ (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.41"
      "Thus, the angle in segment $AHB$ is also equal to $C$."
      (step41 : ∠ a:h:b = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step41 a b d h c₁ c c₂ (by euclid_assumption "" (show ∠ b:a:d = ∠ a:h:b; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∠ c₁:c:c₂; assumption)))

    euclid_sentence "3.33.42"
      "Thus, a segment $AHB$ of a circle, accepting an angle equal to $C$, has been drawn on the given straight-line $AB$."
      (step42 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by euclid_apply (helper_3_33_step42 a b h c₁ c c₂ α (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show h.onCircle α; assumption)) (by euclid_assumption "" (show ∠ a:h:b = ∠ c₁:c:c₂; assumption)))

    exact step42

  euclid_conclude_sentence "3.33.43"
    "(Which is) the very thing it was required to do."

end Elements.Book3
