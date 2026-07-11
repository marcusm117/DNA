import SystemE
import Book3.Prop01.Main
import Book1.Prop11.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_17 : ∀ (a : Point) (BCD : Circle),
  a.outsideCircle BCD →
  ∃ L : Line, a.onLine L ∧ (∃ p : Point, p.onLine L ∧ p.onCircle BCD) ∧ ¬ L.intersectsCircle BCD :=
by
  euclid_intros
  euclid_intro_sentence "3.17.0"
    "To draw a straight-line touching a given circle from a given point. Let $A$ be the given point, and $BCD$ the given circle. So it is required to draw a straight-line touching circle $BCD$ from point $A$."

  euclid_apply (proposition_1 BCD) as e

  euclid_sentence "3.17.1"
    "For let the center $E$ of the circle be found [Prop.~3.1],"
    (step1 : e.isCentre BCD) := by sorry

  have hane : a ≠ e := by sorry
  euclid_apply (line_from_points a e) as AE

  euclid_sentence "3.17.2"
    "and let $AE$ be joined."
    (step2 : distinctPointsOnLine a e AE) := by sorry

  have hean : e ≠ a := hane.symm
  euclid_apply (circle_from_points e a) as AFG

  euclid_sentence "3.17.3"
    "And let (the circle) $AFG$ be drawn with center $E$ and radius $EA$."
    (step3 : e.isCentre AFG ∧ a.onCircle AFG) := by sorry

  have hAE_int_BCD : AE.intersectsCircle BCD := by sorry
  have h_near_d : ∃ d : Point, d.onCircle BCD ∧ d.onLine AE ∧ between e d a := by sorry
  obtain ⟨d, hd_onBCD, hd_onAE, hbetween_eda⟩ := h_near_d
  have hbetween_ade : between a d e := (between_symm e d a hbetween_eda).1
  euclid_apply (proposition_11 a e d AE) as f0
  have hdf0ne : d ≠ f0 := by sorry
  euclid_apply (line_from_points d f0) as DF_line
  have hDF_int_AFG : DF_line.intersectsCircle AFG := by sorry
  have h_int_afg := intersections_circle_line AFG DF_line hDF_int_AFG
  obtain ⟨f, f', hf_onAFG, hf_onDF, hf'_onAFG, hf'_onDF, hff'ne⟩ := h_int_afg
  have hdfne : d ≠ f := by sorry
  euclid_apply (line_from_points d f) as DF

  euclid_sentence "3.17.4"
    "And let $DF$ be drawn from from (point) $D$, at right-angles to $EA$ [Prop.~1.11]."
    (step4 : d.onCircle BCD ∧ d.onLine AE ∧ f.onCircle AFG ∧ ¬(f.onLine AE) ∧ ∠ a:d:f = ∟) := by sorry

  have hefne : e ≠ f := by sorry
  euclid_apply (line_from_points e f) as EF
  have hEF_int_BCD : EF.intersectsCircle BCD := by sorry
  have h_int_bcd2 := intersections_circle_line BCD EF hEF_int_BCD
  obtain ⟨b, b', hb_onBCD, hb_onEF, hb'_onBCD, hb'_onEF, hbb'ne⟩ := h_int_bcd2
  have habne : a ≠ b := by sorry
  euclid_apply (line_from_points a b) as AB

  euclid_sentence "3.17.5"
    "And let $EF$ and $AB$ be joined."
    (step5 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine a b AB) := by sorry

  euclid_wts "3.17.6"
    "I say that the (straight-line) $AB$ has been drawn from point $A$ touching circle $BCD$."

  -- @assumption_valid
  have step7_assumption1 : e.isCentre BCD ∧ e.isCentre AFG := by euclid_finish
  -- @assumption ("$E$ is the center of circles $BCD$ and $AFG$", e.isCentre BCD ∧ e.isCentre AFG)
  euclid_sentence "3.17.7"
    "For since $E$ is the center of circles $BCD$ and $AFG$, $EA$ is thus equal to $EF$,"
    (step7 : |(e─a)| = |(e─f)|) := by sorry

  euclid_sentence "3.17.8"
    "and $ED$ to $EB$."
    (step8 : |(e─d)| = |(e─b)|) := by sorry

  euclid_sentence "3.17.9"
    "So the two (straight-lines) $AE$, $EB$ are equal to the two (straight-lines) $FE$, $ED$ (respectively)."
    (step9 : |(a─e)| = |(f─e)| ∧ |(e─b)| = |(e─d)|) := by sorry

  euclid_sentence "3.17.10"
    "And they contain a common angle at $E$."
    (step10 : ∠ a:e:b = ∠ f:e:d) := by sorry

  euclid_sentence "3.17.11"
    "Thus, the base $DF$ is equal to the base $AB$,"
    (step11 : |(d─f)| = |(a─b)|) := by sorry

  euclid_sentence "3.17.12"
    "and triangle $DEF$ is equal to triangle $EBA$,"
    (step12 : Triangle.area △ d:e:f = Triangle.area △ e:b:a) := by sorry

  euclid_sentence "3.17.13"
    "and the remaining angles (are equal) to the (corresponding) remaining angles [Prop.~1.4]."
    (step13 : ∠ e:d:f = ∠ e:b:a ∧ ∠ e:f:d = ∠ e:a:b) := by sorry

  euclid_sentence "3.17.14"
    "Thus, (angle) $EDF$ (is) equal to $EBA$."
    (step14 : ∠ e:d:f = ∠ e:b:a) := by sorry

  euclid_sentence "3.17.15"
    "And $EDF$ (is) a right-angle."
    (step15 : ∠ e:d:f = ∟) := by sorry

  euclid_sentence "3.17.16"
    "Thus, $EBA$ (is) also a right-angle."
    (step16 : ∠ e:b:a = ∟) := by sorry

  euclid_sentence "3.17.17"
    "And $EB$ is a radius."
    (step17 : b.onCircle BCD) := by sorry

  -- @assumption_gap
  have step18_assumption1 : ∀ (p q r : Point) (γ : Circle) (L : Line), r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ → (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ := by sorry
  -- @assumption ("a (straight-line) drawn at right-angles to the diameter of a circle, from its extremity, touches the circle", ∀ (p q r : Point) (γ : Circle) (L : Line), r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ → (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ)
  euclid_sentence "3.17.18"
    "And a (straight-line) drawn at right-angles to the diameter of a circle, from its extremity, touches the circle [Prop.~3.16~corr.]. Thus, $AB$ touches circle $BCD$."
    (step18 : (∃ p : Point, p.onLine AB ∧ p.onCircle BCD) ∧ ¬ AB.intersectsCircle BCD) := by sorry

  use AB
  euclid_conclude_sentence "3.17.19"
    "Thus, the straight-line $AB$ has been drawn touching the given circle $BCD$ from the given point $A$. (Which is) the very thing it was required to do."

end Elements.Book3
