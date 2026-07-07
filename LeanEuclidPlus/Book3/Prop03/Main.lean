import SystemE
import Book3.Prop01.Main
import Book3.Prop03.step1
import Book3.Prop03.step2
import Book3.Prop03.step3
import Book3.Prop03.step4
import Book3.Prop03.step5
import Book3.Prop03.step6
import Book3.Prop03.step7
import Book3.Prop03.step9
import Book3.Prop03.step10
import Book3.Prop03.step11
import Book3.Prop03.step12
import Book3.Prop03.step13
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_3 : ∀ (a b e f : Point) (ABC : Circle) (AB CD : Line),
  a.onCircle ABC ∧ b.onCircle ABC ∧ distinctPointsOnLine a b AB ∧
  e.isCentre ABC ∧ e.onLine CD ∧ ¬e.onLine AB ∧
  f.onLine AB ∧ f.onLine CD ∧ between a f b →
  (|(a─f)| = |(f─b)| → ∠ a:f:e = ∟) ∧
  (∠ a:f:e = ∟ → |(a─f)| = |(f─b)|) :=
by
  euclid_intros
  euclid_intro_sentence "3.3.0"
    "In a circle, if any straight-line through the center cuts in half any straight-line not through the center, (then) it also cuts it at right-angles. And (conversely) if it cuts it at right-angles, (then) it also cuts it in half. Let $ABC$ be a circle, and, within it, let some straight-line through the center, $CD$, cut in half some straight-line not through the center, $AB$, at the point $F$. I say that ($CD$) also cuts ($AB$) at right-angles."

  euclid_apply (proposition_1 ABC) as e'
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_sentence "3.3.1"
    "For let the center of the circle $ABC$ be found [Prop.~3.1], and let it be (at point) $E$, and let $EA$ and $EB$ be joined."
    (step1 : e'.isCentre ABC ∧ e' = e ∧ distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB) := by euclid_apply (helper_3_3_step1 a b e e' ABC AB EA EB (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬e.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show e'.isCentre ABC; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)))

  refine ⟨?_, ?_⟩

  -- Direction 1: bisects → perpendicular
  ·
    intro h1
    -- @assumption_valid
    have step2_assumption1 : |(a─f)| = |(f─b)| := by assumption
    -- @assumption_valid
    have step2_assumption2 : |(f─e)| = |(f─e)| := by rfl
    -- @assumption ("$AF$ is equal to $FB$", |(a─f)| = |(f─b)|)
    -- @assumption ("$FE$ (is) common", |(f─e)| = |(f─e)|)
    euclid_sentence "3.3.2"
      "And since $AF$ is equal to $FB$, and $FE$ (is) common, two (sides of triangle $AFE$) [are] equal to two (sides of triangle $BFE$)."
      (step2 : |(a─f)| = |(f─b)| ∧ |(f─e)| = |(f─e)|) := by euclid_apply (helper_3_3_step2 a b f e (by euclid_assumption "$AF$ is equal to $FB$" (show |(a─f)| = |(f─b)|; assumption)) (by euclid_assumption "$FE$ (is) common" (show |(f─e)| = |(f─e)|; assumption)))

    euclid_sentence "3.3.3"
      "And the base $EA$ (is) equal to the base $EB$."
      (step3 : |(e─a)| = |(e─b)|) := by euclid_apply (helper_3_3_step3 a b e ABC (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)))

    euclid_sentence "3.3.4"
      "Thus, angle $AFE$ is equal to angle $BFE$ [Prop.~1.8]."
      (step4 : ∠ a:f:e = ∠ b:f:e) := by euclid_apply (helper_3_3_step4 a b e f AB CD EA EB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine CD; assumption)) (by euclid_assumption "" (show f.onLine CD; assumption)) (by euclid_assumption "" (show ¬e.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─b)| ∧ |(f─e)| = |(f─e)|; assumption)) (by euclid_assumption "" (show |(e─a)| = |(e─b)|; assumption)))

    -- @assumption_valid
    have step5_assumption1 : ∠ a:f:e = ∠ b:f:e := by assumption
    -- @assumption ("when a straight-line stood upon (another) straight-line makes adjacent angles (which are) equal to one another", ∠ a:f:e = ∠ b:f:e)
    euclid_sentence "3.3.5"
      "And when a straight-line stood upon (another) straight-line makes adjacent angles (which are) equal to one another, each of the equal angles is a right-angle [Def.~1.10]."
      (step5 : ∠ a:f:e = ∟ ∧ ∠ b:f:e = ∟) := by euclid_apply (helper_3_3_step5 a b e f AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show ¬e.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "when a straight-line stood upon (another) straight-line makes adjacent angles (which are) equal to one another" (show ∠ a:f:e = ∠ b:f:e; assumption)))

    euclid_sentence "3.3.6"
      "Thus, $AFE$ and $BFE$ are each right-angles."
      (step6 : ∠ a:f:e = ∟ ∧ ∠ b:f:e = ∟) := by euclid_apply (helper_3_3_step6 a b e f (by euclid_assumption "" (show ∠ a:f:e = ∟ ∧ ∠ b:f:e = ∟; assumption)))

    euclid_sentence "3.3.7"
      "Thus, the (straight-line) $CD$, which is through the center and cuts in half the (straight-line) $AB$, which is not through the center, also cuts ($AB$) at right-angles."
      (step7 : ∠ a:f:e = ∟) := by euclid_apply (helper_3_3_step7 a b e f (by euclid_assumption "" (show ∠ a:f:e = ∟ ∧ ∠ b:f:e = ∟; assumption)))

    exact step7

  -- Direction 2: perpendicular → bisects
  ·
    intro h2
    euclid_wts "3.3.8"
      "And so let $CD$ cut $AB$ at right-angles. I say that it also cuts ($AB$) in half. That is to say, that $AF$ is equal to $FB$."

    -- @assumption_valid
    have step9_assumption1 : |(e─a)| = |(e─b)| := by euclid_finish
    -- @assumption ("$EA$ is equal to $EB$", |(e─a)| = |(e─b)|)
    euclid_sentence "3.3.9"
      "For, with the same construction, since $EA$ is equal to $EB$, angle $EAF$ is also equal to $EBF$ [Prop.~1.5]."
      (step9 : ∠ e:a:f = ∠ e:b:f) := by euclid_apply (helper_3_3_step9 a b e f AB EA EB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show ¬e.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "$EA$ is equal to $EB$" (show |(e─a)| = |(e─b)|; assumption)))

    -- @assumption_valid
    have step10_assumption1 : ∠ a:f:e = ∟ := by assumption
    -- @assumption ("the right-angle $AFE$", ∠ a:f:e = ∟)
    euclid_sentence "3.3.10"
      "And the right-angle $AFE$ is also equal to the right-angle $BFE$."
      (step10 : ∠ a:f:e = ∠ b:f:e) := by euclid_apply (helper_3_3_step10 a b e f AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show ¬e.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "the right-angle $AFE$" (show ∠ a:f:e = ∟; assumption)))

    euclid_sentence "3.3.11"
      "Thus, $EAF$ and $EFB$ are two triangles having two angles equal to two angles, and one side equal to one side---(namely), their common (side) $EF$, subtending one of the equal angles."
      (step11 : formTriangle e a f EA AB CD ∧ formTriangle e f b CD AB EB ∧
                ∠ e:a:f = ∠ e:b:f ∧ ∠ a:f:e = ∠ b:f:e ∧ |(f─e)| = |(f─e)|) := by euclid_apply (helper_3_3_step11 a b e f AB CD EA EB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine CD; assumption)) (by euclid_assumption "" (show f.onLine CD; assumption)) (by euclid_assumption "" (show ¬e.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ∠ e:a:f = ∠ e:b:f; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∠ b:f:e; assumption)))

    euclid_sentence "3.3.12"
      "Thus, they will also have the remaining sides equal to the (corresponding) remaining sides [Prop.~1.26]."
      (step12 : |(e─a)| = |(e─b)| ∧ |(a─f)| = |(f─b)|) := by euclid_apply (helper_3_3_step12 a b e f AB CD EA EB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine CD; assumption)) (by euclid_assumption "" (show f.onLine CD; assumption)) (by euclid_assumption "" (show ¬e.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show |(e─a)| = |(e─b)|; assumption)) (by euclid_assumption "" (show formTriangle e a f EA AB CD ∧ formTriangle e f b CD AB EB ∧ ∠ e:a:f = ∠ e:b:f ∧ ∠ a:f:e = ∠ b:f:e ∧ |(f─e)| = |(f─e)|; assumption)))

    euclid_sentence "3.3.13"
      "Thus, $AF$ (is) equal to $FB$."
      (step13 : |(a─f)| = |(f─b)|) := by euclid_apply (helper_3_3_step13 a b e f (by euclid_assumption "" (show |(e─a)| = |(e─b)| ∧ |(a─f)| = |(f─b)|; assumption)))

    exact step13

  euclid_conclude_sentence "3.3.14"
    "Thus, in a circle, if any straight-line through the center cuts in half any straight-line not through the center, (then) it also cuts it at right-angles. And (conversely) if it cuts it at right-angles, (then) it also cuts it in half. (Which is) the very thing it was required to show."

end Elements.Book3
