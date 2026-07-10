import SystemE
import Book3.Prop01.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_14 : ∀ (a b c d e f g : Point) (ABDC : Circle) (AB CD : Line),
  a.onCircle ABDC ∧ b.onCircle ABDC ∧ c.onCircle ABDC ∧ d.onCircle ABDC ∧
  e.isCentre ABDC ∧
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧
  f.onLine AB ∧ ∠ a:f:e = ∟ ∧
  g.onLine CD ∧ ∠ c:g:e = ∟ →
  (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
  (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) :=
by
  euclid_intros
  euclid_intro_sentence "3.14.0"
    "In a circle, equal straight-lines are equally far from the center, and (straight-lines) which are equally far from the center are equal to one another. Let $ABDC$$^{\\,\\dag}$ be a circle, and let $AB$ and $CD$ be equal straight-lines within it. I say that $AB$ and $CD$ are equally far from the center."

  by_cases h_ef : e = f
  · -- @euclid_gap: AB is a diameter (foot = centre)
    have gap_ab_diam : (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
                       (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) := by sorry
    exact gap_ab_diam
  by_cases h_eg : e = g
  · -- @euclid_gap: CD is a diameter (foot = centre)
    have gap_cd_diam : (|(a─b)| = |(c─d)| → |(e─f)| = |(e─g)|) ∧
                       (|(e─f)| = |(e─g)| → |(a─b)| = |(c─d)|) := by sorry
    exact gap_cd_diam
  have hef : e ≠ f := h_ef
  have heg : e ≠ g := h_eg
  have hae : a ≠ e := by sorry
  have hec : e ≠ c := by sorry
  euclid_apply (line_from_points e f) as EF
  euclid_apply (line_from_points e g) as EG
  euclid_apply (proposition_1 ABDC) as e'
  euclid_sentence "3.14.1"
    "For let the center of circle $ABDC$ be found [Prop.~3.1], and let it be (at) $E$."
    (step1 : e'.isCentre ABDC ∧ e' = e) := by sorry

  euclid_sentence "3.14.2"
    "And let $EF$ and $EG$ be drawn from (point) $E$, perpendicular to $AB$ and $CD$ (respectively) [Prop.~1.12]."
    (step2 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG
    ∧ ∠ a:f:e = ∟ ∧ ∠ c:g:e = ∟) := by sorry

  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points e c) as EC
  euclid_sentence "3.14.3"
    "And let $AE$ and $EC$ be joined."
    (step3 : distinctPointsOnLine a e AE ∧ distinctPointsOnLine e c EC) := by sorry

  refine ⟨?_, ?_⟩

  · -- Direction 1: equal chords → equal distances
    intro h_ab_eq_cd

    -- @assumption_valid
    have step4_assumption1 : e.onLine EF ∧ f.onLine EF ∧ ∠ a:f:e = ∟ := by euclid_finish
    -- @assumption ("some straight-line, $EF$, through the center (of the circle), cuts some (other) straight-line, $AB$, not through the center, at right-angles", e.onLine EF ∧ f.onLine EF ∧ ∠ a:f:e = ∟)
    euclid_sentence "3.14.4"
      "Therefore, since some straight-line, $EF$, through the center (of the circle), cuts some (other) straight-line, $AB$, not through the center, at right-angles, it also cuts it in half [Prop.~3.3]."
      (step4 : |(a─f)| = |(f─b)|) := by sorry

    euclid_sentence "3.14.5"
      "Thus, $AF$ (is) equal to $FB$."
      (step5 : |(a─f)| = |(f─b)|) := by sorry

    euclid_sentence "3.14.6"
      "Thus, $AB$ (is) double $AF$."
      (step6 : |(a─b)| = |(a─f)| + |(a─f)|) := by sorry

    euclid_sentence "3.14.7"
      "So, for the same (reasons), $CD$ is also double $CG$."
      (step7 : |(c─d)| = |(c─g)| + |(c─g)|) := by sorry

    -- @assumption_valid
    have step8_assumption1 : |(a─b)| = |(c─d)| := by assumption
    -- @assumption ("$AB$ is equal to $CD$", |(a─b)| = |(c─d)|)
    euclid_sentence "3.14.8"
      "And $AB$ is equal to $CD$. Thus, $AF$ (is) also equal to $CG$."
      (step8 : |(a─f)| = |(c─g)|) := by sorry

    -- @assumption_valid
    have step9_assumption1 : |(a─e)| = |(e─c)| := by euclid_finish
    -- @assumption ("$AE$ is equal to $EC$", |(a─e)| = |(e─c)|)
    euclid_sentence "3.14.9"
      "And since $AE$ is equal to $EC$, the (square) on $AE$ (is) also equal to the (square) on $EC$."
      (step9 : |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)|) := by sorry

    -- @assumption_valid
    have step10_assumption1 : ∠ a:f:e = ∟ := by assumption
    -- @assumption ("the angle at $F$ (is) a right-angle", ∠ a:f:e = ∟)
    euclid_sentence "3.14.10"
      "But, the (sum of the squares) on $AF$ and $EF$ (is) equal to the (square) on $AE$. For the angle at $F$ (is) a right-angle [Prop.~1.47]."
      (step10 : |(a─f)| * |(a─f)| + |(e─f)| * |(e─f)| = |(a─e)| * |(a─e)|) := by sorry

    -- @assumption_valid
    have step11_assumption1 : ∠ c:g:e = ∟ := by assumption
    -- @assumption ("the angle at $G$ (is) a right-angle", ∠ c:g:e = ∟)
    euclid_sentence "3.14.11"
      "And the (sum of the squares) on $EG$ and $GC$ (is) equal to the (square) on $EC$. For the angle at $G$ (is) a right-angle [Prop.~1.47]."
      (step11 : |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)|) := by sorry

    -- @assumption_valid
    have step12_assumption1 : |(a─f)| = |(c─g)| := by assumption
    -- @assumption ("$AF$ is equal to $CG$", |(a─f)| = |(c─g)|)
    euclid_sentence "3.14.12"
      "Thus, the (sum of the squares) on $AF$ and $FE$ is equal to the (sum of the squares) on $CG$ and $GE$, of which the (square) on $AF$ is equal to the (square) on $CG$. For $AF$ is equal to $CG$."
      (step12 : |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| = |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| ∧
                |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|) := by sorry

    euclid_sentence "3.14.13"
      "Thus, the remaining (square) on $FE$ is equal to the (remaining square) on $EG$."
      (step13 : |(f─e)| * |(f─e)| = |(e─g)| * |(e─g)|) := by sorry

    euclid_sentence "3.14.14"
      "Thus, $EF$ (is) equal to $EG$."
      (step14 : |(e─f)| = |(e─g)|) := by sorry

    -- @assumption_valid
    have step15_assumption1 : |(e─f)| = |(e─g)| := by assumption
    -- @assumption ("straight-lines in a circle are said to be equally far from the center when perpendicular (straight-lines) which are drawn to them from the center are equal", |(e─f)| = |(e─g)|)
    euclid_sentence "3.14.15"
      "And straight-lines in a circle are said to be equally far from the center when perpendicular (straight-lines) which are drawn to them from the center are equal [Def.~3.4]. Thus, $AB$ and $CD$ are equally far from the center."
      (step15 : |(e─f)| = |(e─g)|) := by sorry

    exact step15

  · -- Direction 2: equal distances → equal chords
    intro h_ef_eq_eg
    
    euclid_sentence "3.14.16"
      "So, let the straight-lines $AB$ and $CD$ be equally far from the center. That is to say, let $EF$ be equal to $EG$."
      (step16 : |(e─f)| = |(e─g)|) := by sorry

    euclid_wts "3.14.17"
      "I say that $AB$ is also equal to $CD$."

    euclid_sentence "3.14.18"
      "For, with the same construction, we can, similarly, show that $AB$ is double $AF$, and $CD$ (double) $CG$."
      (step18 : |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)|) := by sorry

    -- @assumption_valid
    have step19_assumption1 : |(a─e)| = |(e─c)| := by euclid_finish
    -- @assumption ("$AE$ is equal to $CE$", |(a─e)| = |(e─c)|)
    euclid_sentence "3.14.19"
      "And since $AE$ is equal to $CE$, the (square) on $AE$ is equal to the (square) on $CE$."
      (step19 : |(a─e)| * |(a─e)| = |(e─c)| * |(e─c)|) := by sorry

    euclid_sentence "3.14.20"
      "But, the (sum of the squares) on $EF$ and $FA$ is equal to the (square) on $AE$ [Prop.~1.47]."
      (step20 : |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(a─e)| * |(a─e)|) := by sorry

    euclid_sentence "3.14.21"
      "And the (sum of the squares) on $EG$ and $GC$ (is) equal to the (square) on $CE$ [Prop.~1.47]."
      (step21 : |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)|) := by sorry

    -- @assumption_valid
    have step22_assumption1 : |(e─f)| = |(e─g)| := by assumption
    -- @assumption ("$EF$ (is) equal to $EG$", |(e─f)| = |(e─g)|)
    euclid_sentence "3.14.22"
      "Thus, the (sum of the squares) on $EF$ and $FA$ is equal to the (sum of the squares) on $EG$ and $GC$, of which the (square) on $EF$ is equal to the (square) on $EG$. For $EF$ (is) equal to $EG$."
      (step22 : |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| = |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| ∧
                |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)|) := by sorry

    euclid_sentence "3.14.23"
      "Thus, the remaining (square) on $AF$ is equal to the (remaining square) on $CG$."
      (step23 : |(a─f)| * |(a─f)| = |(c─g)| * |(c─g)|) := by sorry

    euclid_sentence "3.14.24"
      "Thus, $AF$ (is) equal to $CG$."
      (step24 : |(a─f)| = |(c─g)|) := by sorry

    -- @assumption_valid
    have step25_assumption1 : |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)| := by assumption
    -- @assumption ("$AB$ is double $AF$, and $CD$ double $CG$", |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)|)
    euclid_sentence "3.14.25"
      "And $AB$ is double $AF$, and $CD$ double $CG$. Thus, $AB$ (is) equal to $CD$."
      (step25 : |(a─b)| = |(c─d)|) := by sorry

    exact step25

  euclid_conclude_sentence "3.14.26"
    "Thus, in a circle, equal straight-lines are equally far from the center, and (straight-lines) which are equally far from the center are equal to one another. (Which is) the very thing it was required to show."

end Elements.Book3
