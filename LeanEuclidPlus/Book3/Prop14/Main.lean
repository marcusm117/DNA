import SystemE
import Book3.Prop01.Main
import Book3.Prop14.step1
import Book3.Prop14.step2
import Book3.Prop14.step3
import Book3.Prop14.step4
import Book3.Prop14.step5
import Book3.Prop14.step6
import Book3.Prop14.step7
import Book3.Prop14.step8
import Book3.Prop14.step9
import Book3.Prop14.step10
import Book3.Prop14.step11
import Book3.Prop14.step12
import Book3.Prop14.step13
import Book3.Prop14.step14
import Book3.Prop14.step15
import Book3.Prop14.step16
import Book3.Prop14.step18
import Book3.Prop14.step19
import Book3.Prop14.step20
import Book3.Prop14.step21
import Book3.Prop14.step22
import Book3.Prop14.step23
import Book3.Prop14.step24
import Book3.Prop14.step25
import Book3.Prop14.gap_ab_diam
import Book3.Prop14.gap_cd_diam
import Book3.Prop14.hae
import Book3.Prop14.hec
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_14 : ∀ (a b c d e f g : Point) (ABDC : Circle) (AB CD : Line),
  a.onCircle ABDC ∧ b.onCircle ABDC ∧ c.onCircle ABDC ∧ d.onCircle ABDC ∧
  e.isCentre ABDC ∧
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  f.onLine AB ∧ ∠ a:f:e = ∟ ∧ between a f b ∧
  g.onLine CD ∧ ∠ c:g:e = ∟ ∧ between c g d →
  (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
  (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) :=
by
  euclid_intros
  euclid_intro_sentence "3.14.0"
    "In a circle, equal straight-lines are equally far from the center, and (straight-lines) which are equally far from the center are equal to one another. Let $ABDC$$^{\\,\\dag}$ be a circle, and let $AB$ and $CD$ be equal straight-lines within it. I say that $AB$ and $CD$ are equally far from the center."

  by_cases h_ef : e = f
  -- @euclid_gap: AB is a diameter (foot = centre)
  ·
    have gap_ab_diam : (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
                       (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) := by euclid_apply (helper_3_14_gap_ab_diam a b c d e f g ABDC AB CD (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show g.onLine CD; assumption)) (by euclid_assumption "" (show ∠ c:g:e = ∟; assumption)) (by euclid_assumption "" (show between c g d; assumption)) (by euclid_assumption "" (show e = f; assumption)))
    exact gap_ab_diam
  by_cases h_eg : e = g
  -- @euclid_gap: CD is a diameter (foot = centre)
  ·
    have gap_cd_diam : (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
                       (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) := by euclid_apply (helper_3_14_gap_cd_diam a b c d e f g ABDC AB CD (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show g.onLine CD; assumption)) (by euclid_assumption "" (show ∠ c:g:e = ∟; assumption)) (by euclid_assumption "" (show between c g d; assumption)) (by euclid_assumption "" (show e = g; assumption)))
    exact gap_cd_diam
  have hef : e ≠ f := h_ef
  have heg : e ≠ g := h_eg
  have hae : a ≠ e := by euclid_apply (helper_3_14_hae a e ABDC (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)))
  have hec : e ≠ c := by euclid_apply (helper_3_14_hec c e ABDC (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)))
  euclid_apply (line_from_points e f) as EF
  euclid_apply (line_from_points e g) as EG
  euclid_apply (proposition_1 ABDC) as e'
  euclid_sentence "3.14.1"
    "For let the center of circle $ABDC$ be found [Prop.~3.1], and let it be (at) $E$."
    (step1 : e'.isCentre ABDC ∧ e' = e) := by euclid_apply (helper_3_14_step1 e e' ABDC (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show e'.isCentre ABDC; assumption)))

  euclid_sentence "3.14.2"
    "And let $EF$ and $EG$ be drawn from (point) $E$, perpendicular to $AB$ and $CD$ (respectively) [Prop.~1.12]."
    (step2 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG
    ∧ ∠ a:f:e = ∟ ∧ ∠ c:g:e = ∟) := by euclid_apply (helper_3_14_step2 a b c d e f g ABDC AB CD EF EG (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show e ≠ g; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine CD; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show between c g d; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:g:e = ∟; assumption)))

  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points e c) as EC
  euclid_sentence "3.14.3"
    "And let $AE$ and $EC$ be joined."
    (step3 : distinctPointsOnLine a e AE ∧ distinctPointsOnLine e c EC) := by euclid_apply (helper_3_14_step3 a c e AE EC (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)))

  refine ⟨?_, ?_⟩

  -- Direction 1: equal chords → equal distances
  · intro h_ab_eq_cd

    -- @assumption_valid
    have step4_assumption1 : e.onLine EF ∧ f.onLine EF ∧ ∠ a:f:e = ∟ := by euclid_finish
    -- @assumption ("some straight-line, $EF$, through the center (of the circle), cuts some (other) straight-line, $AB$, not through the center, at right-angles", e.onLine EF ∧ f.onLine EF ∧ ∠ a:f:e = ∟)
    euclid_sentence "3.14.4"
      "Therefore, since some straight-line, $EF$, through the center (of the circle), cuts some (other) straight-line, $AB$, not through the center, at right-angles, it also cuts it in half [Prop.~3.3]."
      (step4 : |(a─f)| = |(f─b)|) := by euclid_apply (helper_3_14_step4 a b e f ABDC AB EF (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "some straight-line, $EF$, through the center (of the circle), cuts some (other) straight-line, $AB$, not through the center, at right-angles" (show e.onLine EF ∧ f.onLine EF ∧ ∠ a:f:e = ∟; assumption)))

    euclid_sentence "3.14.5"
      "Thus, $AF$ (is) equal to $FB$."
      (step5 : |(a─f)| = |(f─b)|) := by euclid_apply (helper_3_14_step5 a b f (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)))

    euclid_sentence "3.14.6"
      "Thus, $AB$ (is) double $AF$."
      (step6 : |(a─b)| = |(a─f)| + |(a─f)|) := by euclid_apply (helper_3_14_step6 a b f (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)|; assumption)))

    euclid_sentence "3.14.7"
      "So, for the same (reasons), $CD$ is also double $CG$."
      (step7 : |(c─d)| = |(c─g)| + |(c─g)|) := by euclid_apply (helper_3_14_step7 c d e g ABDC CD EG (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine CD; assumption)) (by euclid_assumption "" (show between c g d; assumption)) (by euclid_assumption "" (show e ≠ g; assumption)) (by euclid_assumption "" (show ∠ c:g:e = ∟; assumption)))

    -- @assumption_valid
    have step8_assumption1 : |(a─b)| = |(c─d)| := by assumption
    -- @assumption ("$AB$ is equal to $CD$", |(a─b)| = |(c─d)|)
    euclid_sentence "3.14.8"
      "And $AB$ is equal to $CD$. Thus, $AF$ (is) also equal to $CG$."
      (step8 : |(a─f)| = |(c─g)|) := by euclid_apply (helper_3_14_step8 a b c d f g (by euclid_assumption "" (show |(a─b)| = |(a─f)| + |(a─f)|; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─g)| + |(c─g)|; assumption)) (by euclid_assumption "$AB$ is equal to $CD$" (show |(a─b)| = |(c─d)|; assumption)))

    -- @assumption_valid
    have step9_assumption1 : |(a─e)| = |(e─c)| := by euclid_finish
    -- @assumption ("$AE$ is equal to $EC$", |(a─e)| = |(e─c)|)
    euclid_sentence "3.14.9"
      "And since $AE$ is equal to $EC$, the (square) on $AE$ (is) also equal to the (square) on $EC$."
      (step9 : |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)|) := by euclid_apply (helper_3_14_step9 a c e (by euclid_assumption "$AE$ is equal to $EC$" (show |(a─e)| = |(e─c)|; assumption)))

    -- @assumption_valid
    have step10_assumption1 : ∠ a:f:e = ∟ := by assumption
    -- @assumption ("the angle at $F$ (is) a right-angle", ∠ a:f:e = ∟)
    euclid_sentence "3.14.10"
      "But, the (sum of the squares) on $AF$ and $EF$ (is) equal to the (square) on $AE$. For the angle at $F$ (is) a right-angle [Prop.~1.47]."
      (step10 : |(a─f)| * |(a─f)| + |(e─f)| * |(e─f)| = |(a─e)| * |(a─e)|) := by euclid_apply (helper_3_14_step10 a b e f ABDC AB (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "the angle at $F$ (is) a right-angle" (show ∠ a:f:e = ∟; assumption)))

    -- @assumption_valid
    have step11_assumption1 : ∠ c:g:e = ∟ := by assumption
    -- @assumption ("the angle at $G$ (is) a right-angle", ∠ c:g:e = ∟)
    euclid_sentence "3.14.11"
      "And the (sum of the squares) on $EG$ and $GC$ (is) equal to the (square) on $EC$. For the angle at $G$ (is) a right-angle [Prop.~1.47]."
      (step11 : |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)|) := by euclid_apply (helper_3_14_step11 c d e g ABDC CD (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show g.onLine CD; assumption)) (by euclid_assumption "" (show between c g d; assumption)) (by euclid_assumption "" (show e ≠ g; assumption)) (by euclid_assumption "the angle at $G$ (is) a right-angle" (show ∠ c:g:e = ∟; assumption)))

    -- @assumption_valid
    have step12_assumption1 : |(a─f)| = |(c─g)| := by assumption
    -- @assumption ("$AF$ is equal to $CG$", |(a─f)| = |(c─g)|)
    euclid_sentence "3.14.12"
      "Thus, the (sum of the squares) on $AF$ and $FE$ is equal to the (sum of the squares) on $CG$ and $GE$, of which the (square) on $AF$ is equal to the (square) on $CG$. For $AF$ is equal to $CG$."
      (step12 : |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| ∧
                |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|) := by euclid_apply (helper_3_14_step12 a c e f g (by euclid_assumption "" (show |(a─f)| * |(a─f)| + |(e─f)| * |(e─f)| = |(a─e)| * |(a─e)|; assumption)) (by euclid_assumption "" (show |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)|; assumption)) (by euclid_assumption "$AF$ is equal to $CG$" (show |(a─f)| = |(c─g)|; assumption)))

    euclid_sentence "3.14.13"
      "Thus, the remaining (square) on $FE$ is equal to the (remaining square) on $EG$."
      (step13 : |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)|) := by euclid_apply (helper_3_14_step13 a c e f g (by euclid_assumption "" (show |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| ∧ |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|; assumption)))

    euclid_sentence "3.14.14"
      "Thus, $EF$ (is) equal to $EG$."
      (step14 : |(e─f)| = |(e─g)|) := by euclid_apply (helper_3_14_step14 e f g (by euclid_assumption "" (show |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)|; assumption)))

    -- @assumption_valid
    have step15_assumption1 : |(e─f)| = |(e─g)| := by assumption
    -- @assumption ("straight-lines in a circle are said to be equally far from the center when perpendicular (straight-lines) which are drawn to them from the center are equal", |(e─f)| = |(e─g)|)
    euclid_sentence "3.14.15"
      "And straight-lines in a circle are said to be equally far from the center when perpendicular (straight-lines) which are drawn to them from the center are equal [Def.~3.4]. Thus, $AB$ and $CD$ are equally far from the center."
      (step15 : |(e─f)| = |(e─g)|) := by euclid_apply (helper_3_14_step15 e f g (by euclid_assumption "straight-lines in a circle are said to be equally far from the center when perpendicular (straight-lines) which are drawn to them from the center are equal" (show |(e─f)| = |(e─g)|; assumption)))

    exact step15

  -- Direction 2: equal distances → equal chords
  · intro h_ef_eq_eg
    
    euclid_sentence "3.14.16"
      "So, let the straight-lines $AB$ and $CD$ be equally far from the center. That is to say, let $EF$ be equal to $EG$."
      (step16 : |(e─f)| = |(e─g)|) := by euclid_apply (helper_3_14_step16 e f g (by euclid_assumption "" (show |(e─f)| = |(e─g)|; assumption)))

    euclid_wts "3.14.17"
      "I say that $AB$ is also equal to $CD$."

    euclid_sentence "3.14.18"
      "For, with the same construction, we can, similarly, show that $AB$ is double $AF$, and $CD$ (double) $CG$."
      (step18 : |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)|) := by euclid_apply (helper_3_14_step18 a b c d e f g ABDC AB CD EF EG (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show g.onLine CD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show between c g d; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show e ≠ g; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:g:e = ∟; assumption)))

    -- @assumption_valid
    have step19_assumption1 : |(a─e)| = |(e─c)| := by euclid_finish
    -- @assumption ("$AE$ is equal to $CE$", |(a─e)| = |(e─c)|)
    euclid_sentence "3.14.19"
      "And since $AE$ is equal to $CE$, the (square) on $AE$ is equal to the (square) on $CE$."
      (step19 : |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)|) := by euclid_apply (helper_3_14_step19 a c e (by euclid_assumption "$AE$ is equal to $CE$" (show |(a─e)| = |(e─c)|; assumption)))

    euclid_sentence "3.14.20"
      "But, the (sum of the squares) on $EF$ and $FA$ is equal to the (square) on $AE$ [Prop.~1.47]."
      (step20 : |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(a─e)| * |(a─e)|) := by euclid_apply (helper_3_14_step20 a b e f ABDC AB (by euclid_assumption "" (show a.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)))

    euclid_sentence "3.14.21"
      "And the (sum of the squares) on $EG$ and $GC$ (is) equal to the (square) on $CE$ [Prop.~1.47]."
      (step21 : |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)|) := by euclid_apply (helper_3_14_step21 c d e g ABDC CD (by euclid_assumption "" (show c.onCircle ABDC; assumption)) (by euclid_assumption "" (show e.isCentre ABDC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show g.onLine CD; assumption)) (by euclid_assumption "" (show between c g d; assumption)) (by euclid_assumption "" (show e ≠ g; assumption)) (by euclid_assumption "" (show ∠ c:g:e = ∟; assumption)))

    -- @assumption_valid
    have step22_assumption1 : |(e─f)| = |(e─g)| := by assumption
    -- @assumption ("$EF$ (is) equal to $EG$", |(e─f)| = |(e─g)|)
    euclid_sentence "3.14.22"
      "Thus, the (sum of the squares) on $EF$ and $FA$ is equal to the (sum of the squares) on $EG$ and $GC$, of which the (square) on $EF$ is equal to the (square) on $EG$. For $EF$ (is) equal to $EG$."
      (step22 : |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| ∧
                |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)|) := by euclid_apply (helper_3_14_step22 a c e f g (by euclid_assumption "" (show |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(a─e)| * |(a─e)|; assumption)) (by euclid_assumption "" (show |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)|; assumption)) (by euclid_assumption "$EF$ (is) equal to $EG$" (show |(e─f)| = |(e─g)|; assumption)))

    euclid_sentence "3.14.23"
      "Thus, the remaining (square) on $AF$ is equal to the (remaining square) on $CG$."
      (step23 : |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|) := by euclid_apply (helper_3_14_step23 a c e f g (by euclid_assumption "" (show |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| ∧ |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)|; assumption)))

    euclid_sentence "3.14.24"
      "Thus, $AF$ (is) equal to $CG$."
      (step24 : |(a─f)| = |(c─g)|) := by euclid_apply (helper_3_14_step24 a c f g (by euclid_assumption "" (show |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|; assumption)))

    -- @assumption_valid
    have step25_assumption1 : |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)| := by assumption
    -- @assumption ("$AB$ is double $AF$, and $CD$ double $CG$", |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)|)
    euclid_sentence "3.14.25"
      "And $AB$ is double $AF$, and $CD$ double $CG$. Thus, $AB$ (is) equal to $CD$."
      (step25 : |(a─b)| = |(c─d)|) := by euclid_apply (helper_3_14_step25 a b c d f g (by euclid_assumption "" (show |(a─f)| = |(c─g)|; assumption)) (by euclid_assumption "$AB$ is double $AF$, and $CD$ double $CG$" (show |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)|; assumption)))

    exact step25

  euclid_conclude_sentence "3.14.26"
    "Thus, in a circle, equal straight-lines are equally far from the center, and (straight-lines) which are equally far from the center are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book3
