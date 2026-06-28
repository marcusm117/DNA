import SystemE
import Book.Prop45
import Book.Prop03
import Book.Prop10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_14 : ∀ (a b c : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:c := by
  euclid_intros
  euclid_intro_sentence "2.14.0"
    "To construct a square equal to a given rectilinear figure. Let $A$ be the given rectilinear figure. So it is required to construct a square equal to the rectilinear figure $A$."

  euclid_apply (proposition_45 (triangle a b c)) as (b0, e0, c0, d0, BE, CD, BC, ED)
  euclid_sentence "2.14.1"
    "For let the right-angled parallelogram $BD$, equal to the rectilinear figure $A$, be constructed [Prop. 1.45]."
    (step1 : Triangle.area △ b:e:d + Triangle.area △ b:c:d = Triangle.area △ a:b:c ∧ ∠ c:b:e = ∟) := by sorry

  euclid_sentence "2.14.2"
    "Therefore, if $BE$ is equal to $ED$ then that (which) was prescribed has taken place."
    (step2 : |(b─e)| = |(e─d)| → |(b─e)| * |(b─e)| = Triangle.area △ a:b:c) := by sorry

  euclid_sentence "2.14.3"
    "For the square $BD$, equal to the rectilinear figure $A$, has been constructed."
    (step3 : |(b─e)| = |(e─d)| → Triangle.area △ b:e:d + Triangle.area △ b:c:d = |(b─e)| * |(b─e)|) := by sorry

  euclid_sentence "2.14.4"
    "And if not, (then) one of the (straight-lines) $BE$ or $ED$ is greater (than the other)."
    (step4 : |(b─e)| ≠ |(e─d)| → |(b─e)| > |(e─d)| ∨ |(e─d)| > |(b─e)|) := by sorry

  euclid_apply (extend_point_longer BE b e (e─d)) as f
  euclid_sentence "2.14.5"
    "Let $BE$ be greater, and let it be produced to $F$,"
    (step5 : between b e f ∧ f.onLine BE) := by sorry

  euclid_apply (proposition_3 e f e d BE ED) as f0
  euclid_sentence "2.14.6"
    "and let $EF$ be made equal to $ED$ [Prop.~1.3]."
    (step6 : between e f0 f ∧ |(e─f0)| = |(e─d)|) := by sorry

  euclid_apply (proposition_10 b f BE) as g
  euclid_sentence "2.14.7"
    "And let $BF$ be cut in half at (point) $G$ [Prop.~1.10]."
    (step7 : between b g f ∧ |(b─g)| = |(g─f)|) := by sorry

  euclid_apply (circle_from_points g b) as BHF
  euclid_sentence "2.14.8"
    "And, with center $G$, and radius one of the (straight-lines) $GB$ or $GF$, let the semi-circle $BHF$ be drawn."
    (step8 : |(g─h)| = |(g─b)|) := by sorry

  euclid_apply (intersection_circle_line BHF DE) as h
  euclid_sentence "2.14.9"
    "And let $DE$ be produced to $H$,"
    (step9 : h.onLine DE ∧ ¬(between e h d)) := by sorry

  euclid_apply (line_from_points g h) as GH
  euclid_sentence "2.14.10"
    "and let $GH$ be joined."
    (step10 : distinctPointsOnLine g h GH) := by sorry

  -- @assumption ("the straight-line $BF$ has been cut---equally at $G$, and unequally at $E$", |(b─g)| = |(g─f)| ∧ between b e f)
  euclid_sentence "2.14.11"
    "Therefore, since the straight-line $BF$ has been cut---equally at $G$, and unequally at $E$---the rectangle contained by $BE$ and $EF$, plus the square on $EG$, is thus equal to the square on $GF$ [Prop.~2.5]."
    (step11 : |(b─e)| * |(e─f)| + |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)|) := by sorry

  euclid_sentence "2.14.12"
    "And $GF$ (is) equal to $GH$."
    (step12 : |(g─f)| = |(g─h)|) := by sorry

  euclid_sentence "2.14.13"
    "Thus, the (rectangle contained) by $BE$ and $EF$, plus the (square) on $GE$, is equal to the (square) on $GH$."
    (step13 : |(b─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(g─h)| * |(g─h)|) := by sorry

  euclid_sentence "2.14.14"
    "And the (sum of the) squares on $HE$ and $EG$ is equal to the (square) on $GH$ [Prop.~1.47]."
    (step14 : |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)|) := by sorry

  euclid_sentence "2.14.15"
    "Thus, the (rectangle contained) by $BE$ and $EF$, plus the (square) on $GE$, is equal to the (sum of the squares) on $HE$ and $EG$."
    (step15 : |(b─e)| * |(e─f)| + |(g─e)| * |(g─e)| = |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)|) := by sorry

  euclid_sentence "2.14.16"
    "Let the square on $GE$ be taken from both."
    (step16 : |(b─e)| * |(e─f)| = |(h─e)| * |(h─e)|) := by sorry

  euclid_sentence "2.14.17"
    "Thus, the remaining rectangle contained by $BE$ and $EF$ is equal to the square on $EH$."
    (step17 : |(b─e)| * |(e─f)| = |(e─h)| * |(e─h)|) := by sorry

  -- @assumption ("$EF$ (is) equal to $ED$", |(e─f)| = |(e─d)|)
  euclid_sentence "2.14.18"
    "But, $BD$ is the (rectangle contained) by $BE$ and $EF$. For $EF$ (is) equal to $ED$."
    (step18 : Triangle.area △ b:e:d + Triangle.area △ b:c:d = |(b─e)| * |(e─f)|) := by sorry

  euclid_sentence "2.14.19"
    "Thus, the parallelogram $BD$ is equal to the square on $HE$."
    (step19 : Triangle.area △ b:e:d + Triangle.area △ b:c:d = |(h─e)| * |(h─e)|) := by sorry

  euclid_sentence "2.14.20"
    "And $BD$ (is) equal to the rectilinear figure $A$."
    (step20 : Triangle.area △ b:e:d + Triangle.area △ b:c:d = Triangle.area △ a:b:c) := by sorry

  euclid_sentence "2.14.21"
    "Thus, the rectilinear figure $A$ is also equal to the square (which) can be described on $EH$."
    (step21 : |(e─h)| * |(e─h)| = Triangle.area △ a:b:c) := by sorry

  -- NOTE: existential conclusion — `exact step21` won't close the goal.
  -- The existential witness + betweenness/construction proof needs manual fixup.
  sorry
  euclid_conclude_sentence "2.14.22"
    "Thus, a square---(namely), that (which) can be described on $EH$---has been constructed, equal to the given rectilinear figure $A$. (Which is) the very thing it was required to do."

end Elements.Book2
