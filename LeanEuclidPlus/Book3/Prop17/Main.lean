import SystemE
import Book3.Prop01.Main
import Book1.Prop11.Main
import Book3.Prop17.step1
import Book3.Prop17.step2
import Book3.Prop17.step3
import Book3.Prop17.step4
import Book3.Prop17.step5
import Book3.Prop17.step7
import Book3.Prop17.step8
import Book3.Prop17.step9
import Book3.Prop17.step10
import Book3.Prop17.step11
import Book3.Prop17.step12
import Book3.Prop17.step13
import Book3.Prop17.step14
import Book3.Prop17.step15
import Book3.Prop17.step16
import Book3.Prop17.step17
import Book3.Prop17.step18
import Book3.Prop17.hane
import Book3.Prop17.hAE_int_BCD
import Book3.Prop17.h_near_d
import Book3.Prop17.hdf0ne
import Book3.Prop17.hDF_int_AFG
import Book3.Prop17.hdfne
import Book3.Prop17.hefne
import Book3.Prop17.hEF_int_BCD
import Book3.Prop17.hf_out_BCD
import Book3.Prop17.h_near_b
import Book3.Prop17.habne
import Book3.Prop17.step18_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

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
    (step1 : e.isCentre BCD) := by euclid_apply (helper_3_17_step1 e BCD (by euclid_assumption "" (show e.isCentre BCD; assumption)))

  have hane : a ≠ e := by euclid_apply (helper_3_17_hane a e BCD (by euclid_assumption "" (show ¬a.insideCircle BCD; assumption)) (by euclid_assumption "" (show e.isCentre BCD; assumption)))
  euclid_apply (line_from_points a e) as AE

  euclid_sentence "3.17.2"
    "and let $AE$ be joined."
    (step2 : distinctPointsOnLine a e AE) := by euclid_apply (helper_3_17_step2 a e AE (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)))

  have hean : e ≠ a := hane.symm
  euclid_apply (circle_from_points e a) as AFG

  euclid_sentence "3.17.3"
    "And let (the circle) $AFG$ be drawn with center $E$ and radius $EA$."
    (step3 : e.isCentre AFG ∧ a.onCircle AFG) := by euclid_apply (helper_3_17_step3 a e AFG (by euclid_assumption "" (show e.isCentre AFG; assumption)) (by euclid_assumption "" (show a.onCircle AFG; assumption)))

  have hAE_int_BCD : AE.intersectsCircle BCD := by euclid_apply (helper_3_17_hAE_int_BCD e BCD AE (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e.isCentre BCD; assumption)))
  have h_near_d : ∃ d : Point, d.onCircle BCD ∧ d.onLine AE ∧ between e d a := by euclid_apply (helper_3_17_h_near_d a e BCD AE (by euclid_assumption "" (show e.isCentre BCD; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show ¬a.insideCircle BCD; assumption)) (by euclid_assumption "" (show ¬a.onCircle BCD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)))
  obtain ⟨d, hd_onBCD, hd_onAE, hbetween_eda⟩ := h_near_d
  have hbetween_ade : between a d e := (between_symm e d a hbetween_eda).1
  euclid_apply (proposition_11 a e d AE) as f0
  have hdf0ne : d ≠ f0 := by euclid_apply (helper_3_17_hdf0ne d f0 AE (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show ¬f0.onLine AE; assumption)))
  euclid_apply (line_from_points d f0) as DF_line
  have hDF_int_AFG : DF_line.intersectsCircle AFG := by euclid_apply (helper_3_17_hDF_int_AFG a d e BCD AFG DF_line (by euclid_assumption "" (show e.isCentre BCD; assumption)) (by euclid_assumption "" (show e.isCentre AFG; assumption)) (by euclid_assumption "" (show a.onCircle AFG; assumption)) (by euclid_assumption "" (show d.onCircle BCD; assumption)) (by euclid_assumption "" (show d.onLine DF_line; assumption)) (by euclid_assumption "" (show ¬a.insideCircle BCD; assumption)) (by euclid_assumption "" (show ¬a.onCircle BCD; assumption)))
  have h_int_afg := intersections_circle_line AFG DF_line hDF_int_AFG
  obtain ⟨f, f', hf_onAFG, hf_onDF, hf'_onAFG, hf'_onDF, hff'ne⟩ := h_int_afg
  have hdfne : d ≠ f := by euclid_apply (helper_3_17_hdfne a d f e BCD AFG (by euclid_assumption "" (show e.isCentre BCD; assumption)) (by euclid_assumption "" (show e.isCentre AFG; assumption)) (by euclid_assumption "" (show d.onCircle BCD; assumption)) (by euclid_assumption "" (show f.onCircle AFG; assumption)) (by euclid_assumption "" (show a.onCircle AFG; assumption)) (by euclid_assumption "" (show ¬a.insideCircle BCD; assumption)) (by euclid_assumption "" (show ¬a.onCircle BCD; assumption)))
  euclid_apply (line_from_points d f) as DF

  euclid_sentence "3.17.4"
    "And let $DF$ be drawn from from (point) $D$, at right-angles to $EA$ [Prop.~1.11]."
    (step4 : d.onCircle BCD ∧ d.onLine AE ∧ f.onCircle AFG ∧ ¬(f.onLine AE) ∧ ∠ a:d:f = ∟) := by euclid_apply (helper_3_17_step4 a d f f0 BCD AFG AE DF_line (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show d.onCircle BCD; assumption)) (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show f.onCircle AFG; assumption)) (by euclid_assumption "" (show d.onLine DF_line; assumption)) (by euclid_assumption "" (show f.onLine DF_line; assumption)) (by euclid_assumption "" (show f0.onLine DF_line; assumption)) (by euclid_assumption "" (show ¬f0.onLine AE; assumption)) (by euclid_assumption "" (show ∠a:d:f0 = ∟; assumption)) (by euclid_assumption "" (show between a d e; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)) (by euclid_assumption "" (show d ≠ f0; assumption)))

  have hefne : e ≠ f := by euclid_apply (helper_3_17_hefne e f AFG (by euclid_assumption "" (show e.isCentre AFG; assumption)) (by euclid_assumption "" (show f.onCircle AFG; assumption)))
  euclid_apply (line_from_points e f) as EF
  have hEF_int_BCD : EF.intersectsCircle BCD := by euclid_apply (helper_3_17_hEF_int_BCD e BCD EF (by euclid_assumption "" (show e.isCentre BCD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)))
  have hf_out_BCD : f.outsideCircle BCD := by euclid_apply (helper_3_17_hf_out_BCD a d e f BCD AFG (by euclid_assumption "" (show e.isCentre BCD; assumption)) (by euclid_assumption "" (show e.isCentre AFG; assumption)) (by euclid_assumption "" (show a.onCircle AFG; assumption)) (by euclid_assumption "" (show f.onCircle AFG; assumption)) (by euclid_assumption "" (show d.onCircle BCD; assumption)) (by euclid_assumption "" (show ¬a.insideCircle BCD; assumption)) (by euclid_assumption "" (show ¬a.onCircle BCD; assumption)))
  have h_near_b : ∃ b : Point, b.onCircle BCD ∧ b.onLine EF ∧ between e b f := by euclid_apply (helper_3_17_h_near_b e f BCD EF (by euclid_assumption "" (show e.isCentre BCD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.outsideCircle BCD; assumption)))
  obtain ⟨b, hb_onBCD, hb_onEF, hbetween_ebf⟩ := h_near_b
  have habne : a ≠ b := by euclid_apply (helper_3_17_habne a b BCD (by euclid_assumption "" (show ¬a.onCircle BCD; assumption)) (by euclid_assumption "" (show b.onCircle BCD; assumption)))
  euclid_apply (line_from_points a b) as AB

  euclid_sentence "3.17.5"
    "And let $EF$ and $AB$ be joined."
    (step5 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine a b AB) := by euclid_apply (helper_3_17_step5 a b e f EF AB (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)))

  euclid_wts "3.17.6"
    "I say that the (straight-line) $AB$ has been drawn from point $A$ touching circle $BCD$."

  -- @assumption_valid
  have step7_assumption1 : e.isCentre BCD ∧ e.isCentre AFG := by euclid_finish
  -- @assumption ("$E$ is the center of circles $BCD$ and $AFG$", e.isCentre BCD ∧ e.isCentre AFG)
  euclid_sentence "3.17.7"
    "For since $E$ is the center of circles $BCD$ and $AFG$, $EA$ is thus equal to $EF$,"
    (step7 : |(e─a)| = |(e─f)|) := by euclid_apply (helper_3_17_step7 a e f BCD AFG (by euclid_assumption "" (show a.onCircle AFG; assumption)) (by euclid_assumption "" (show f.onCircle AFG; assumption)) (by euclid_assumption "$E$ is the center of circles $BCD$ and $AFG$" (show e.isCentre BCD ∧ e.isCentre AFG; assumption)))

  euclid_sentence "3.17.8"
    "and $ED$ to $EB$."
    (step8 : |(e─d)| = |(e─b)|) := by euclid_apply (helper_3_17_step8 b d e BCD (by euclid_assumption "" (show e.isCentre BCD; assumption)) (by euclid_assumption "" (show d.onCircle BCD; assumption)) (by euclid_assumption "" (show b.onCircle BCD; assumption)))

  euclid_sentence "3.17.9"
    "So the two (straight-lines) $AE$, $EB$ are equal to the two (straight-lines) $FE$, $ED$ (respectively)."
    (step9 : |(a─e)| = |(f─e)| ∧ |(e─b)| = |(e─d)|) := by euclid_apply (helper_3_17_step9 a b d e f (by euclid_assumption "" (show |(e─a)| = |(e─f)|; assumption)) (by euclid_assumption "" (show |(e─d)| = |(e─b)|; assumption)))

  euclid_sentence "3.17.10"
    "And they contain a common angle at $E$."
    (step10 : ∠ a:e:b = ∠ f:e:d) := by euclid_apply (helper_3_17_step10 a b d e f AE EF (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between a d e; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)))

  euclid_sentence "3.17.11"
    "Thus, the base $DF$ is equal to the base $AB$,"
    (step11 : |(d─f)| = |(a─b)|) := by euclid_apply (helper_3_17_step11 a b d e f AE EF AB DF (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show ¬f.onLine AE; assumption)) (by euclid_assumption "" (show between a d e; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show |(a─e)| = |(f─e)| ∧ |(e─b)| = |(e─d)|; assumption)) (by euclid_assumption "" (show ∠ a:e:b = ∠ f:e:d; assumption)))

  euclid_sentence "3.17.12"
    "and triangle $DEF$ is equal to triangle $EBA$,"
    (step12 : Triangle.area △ d:e:f = Triangle.area △ e:b:a) := by euclid_apply (helper_3_17_step12 a b d e f AE EF DF AB (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)) (by euclid_assumption "" (show ¬f.onLine AE; assumption)) (by euclid_assumption "" (show between a d e; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show |(e─a)| = |(e─f)|; assumption)) (by euclid_assumption "" (show |(e─d)| = |(e─b)|; assumption)) (by euclid_assumption "" (show ∠ a:e:b = ∠ f:e:d; assumption)))

  euclid_sentence "3.17.13"
    "and the remaining angles (are equal) to the (corresponding) remaining angles [Prop.~1.4]."
    (step13 : ∠ e:d:f = ∠ e:b:a ∧ ∠ e:f:d = ∠ e:a:b) := by euclid_apply (helper_3_17_step13 a b d e f AE EF DF AB (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)) (by euclid_assumption "" (show ¬f.onLine AE; assumption)) (by euclid_assumption "" (show between a d e; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show |(e─a)| = |(e─f)|; assumption)) (by euclid_assumption "" (show |(e─d)| = |(e─b)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─b)|; assumption)))

  euclid_sentence "3.17.14"
    "Thus, (angle) $EDF$ (is) equal to $EBA$."
    (step14 : ∠ e:d:f = ∠ e:b:a) := by euclid_apply (helper_3_17_step14 e d f b a (by euclid_assumption "" (show ∠ e:d:f = ∠ e:b:a ∧ ∠ e:f:d = ∠ e:a:b; assumption)))

  euclid_sentence "3.17.15"
    "And $EDF$ (is) a right-angle."
    (step15 : ∠ e:d:f = ∟) := by euclid_apply (helper_3_17_step15 a d e f AE (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine AE; assumption)) (by euclid_assumption "" (show ¬f.onLine AE; assumption)) (by euclid_assumption "" (show between a d e; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)))

  euclid_sentence "3.17.16"
    "Thus, $EBA$ (is) also a right-angle."
    (step16 : ∠ e:b:a = ∟) := by euclid_apply (helper_3_17_step16 e b a d f (by euclid_assumption "" (show ∠ e:d:f = ∠ e:b:a; assumption)) (by euclid_assumption "" (show ∠ e:d:f = ∟; assumption)))

  euclid_sentence "3.17.17"
    "And $EB$ is a radius."
    (step17 : b.onCircle BCD) := by euclid_apply (helper_3_17_step17 b BCD (by euclid_assumption "" (show b.onCircle BCD; assumption)))

  -- @assumption_gap
  have step18_assumption1 : ∀ (p q r : Point) (γ : Circle) (L : Line), r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ → (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ := by euclid_apply (helper_3_17_step18_assumption1 )
  -- @assumption ("a (straight-line) drawn at right-angles to the diameter of a circle, from its extremity, touches the circle", ∀ (p q r : Point) (γ : Circle) (L : Line), r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ → (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ)
  euclid_sentence "3.17.18"
    "And a (straight-line) drawn at right-angles to the diameter of a circle, from its extremity, touches the circle [Prop.~3.16~corr.]. Thus, $AB$ touches circle $BCD$."
    (step18 : (∃ p : Point, p.onLine AB ∧ p.onCircle BCD) ∧ ¬ AB.intersectsCircle BCD) := by euclid_apply (helper_3_17_step18 b a e BCD AB (by euclid_assumption "" (show e.isCentre BCD; assumption)) (by euclid_assumption "" (show ∠ e:b:a = ∟; assumption)) (by euclid_assumption "" (show b.onCircle BCD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "a (straight-line) drawn at right-angles to the diameter of a circle, from its extremity, touches the circle" (show ∀ (p q r : Point) (γ : Circle) (L : Line), r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ → (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ; assumption)))

  use AB
  euclid_conclude_sentence "3.17.19"
    "Thus, the straight-line $AB$ has been drawn touching the given circle $BCD$ from the given point $A$. (Which is) the very thing it was required to do."

end Elements.Book3
