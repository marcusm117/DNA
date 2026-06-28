import SystemE
import Book.Prop46
import Book.Prop10
import Book.Prop03
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_11 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ h : Point, between a h b ∧
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| := by
  euclid_intros
  euclid_intro_sentence "2.11.0"
    "To cut a given straight-line such that the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the square on the remaining piece. Let $AB$ be the given straight-line. So it is required to cut $AB$ such that the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the square on the remaining piece."

  euclid_apply (proposition_46 a b AB) as (c, d, CD, AC, BD)
  euclid_sentence "2.11.1"
    "For let the square $ABDC$ be described on $AB$ [Prop.~1.46],"
    (step1 : formParallelogram c d a b CD AB AC BD ∧ |(c─d)| = |(a─b)| ∧ |(a─c)| = |(a─b)| ∧ |(b─d)| = |(a─b)| ∧ ∠ b:a:c = ∟ ∧ ∠ a:c:d = ∟ ∧ ∠ a:b:d = ∟ ∧ ∠ c:d:b = ∟) := by sorry

  euclid_apply (proposition_10 a c AC) as e
  euclid_sentence "2.11.2"
    "and let $AC$ be cut in half at point $E$ [Prop.~1.10],"
    (step2 : between a e c ∧ |(a─e)| = |(e─c)|) := by sorry

  euclid_apply (line_from_points b e) as BE
  euclid_sentence "2.11.3"
    "and let $BE$ be joined."
    (step3 : distinctPointsOnLine b e BE) := by sorry

  euclid_apply (extend_point_longer AC c a (b─e)) as f0
  euclid_sentence "2.11.4"
    "And let $CA$ be drawn through to (point) $F$,"
    (step4 : between c a f0 ∧ f0.onLine AC) := by sorry

  euclid_apply (proposition_3 e f0 b e AC BE) as f
  euclid_sentence "2.11.5"
    "and let $EF$ be made equal to $BE$ [Prop.~1.3]."
    (step5 : between e f f0 ∧ |(e─f)| = |(b─e)|) := by sorry

  euclid_apply (proposition_46 a f AC) as (h, g, GH, AH, FG)
  euclid_sentence "2.11.6"
    "And let the square $FH$ be described on $AF$ [Prop.~1.46],"
    (step6 : formParallelogram h g a f GH AC AH FG ∧ |(h─g)| = |(a─f)| ∧ |(a─h)| = |(a─f)| ∧ |(f─g)| = |(a─f)| ∧ ∠ f:a:h = ∟ ∧ ∠ a:f:g = ∟ ∧ ∠ a:h:g = ∟ ∧ ∠ f:g:h = ∟) := by sorry

  euclid_apply (intersection_lines GH CD) as k
  euclid_sentence "2.11.7"
    "and let $GH$ be drawn through to (point) $K$."
    (step7 : k.onLine GH ∧ k.onLine CD) := by sorry

  euclid_sentence "2.11.8"
    "I say that $AB$ has been cut at $H$ such as to make the rectangle contained by $AB$ and $BH$ equal to the square on $AH$."
    (step8 : |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)|) := by sorry

  -- @assumption ("the straight-line $AC$ has been cut in half at $E$, and $FA$ has been added to it", |(a─e)| = |(e─c)| ∧ between c a f)
  euclid_sentence "2.11.9"
    "For since the straight-line $AC$ has been cut in half at $E$, and $FA$ has been added to it, the rectangle contained by $CF$ and $FA$, plus the square on $AE$, is thus equal to the square on $EF$ [Prop.~2.6]."
    (step9 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─f)| * |(e─f)|) := by sorry

  euclid_sentence "2.11.10"
    "And $EF$ (is) equal to $EB$."
    (step10 : |(e─f)| = |(e─b)|) := by sorry

  euclid_sentence "2.11.11"
    "Thus, the (rectangle contained) by $CF$ and $FA$, plus the (square) on $AE$, is equal to the (square) on $EB$."
    (step11 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)|) := by sorry

  -- @assumption ("the angle at $A$ (is) a right-angle", ∠ b:a:c = ∟)
  euclid_sentence "2.11.12"
    "But, the (sum of the squares) on $BA$ and $AE$ is equal to the (square) on $EB$. For the angle at $A$ (is) a right-angle [Prop.~1.47]."
    (step12 : |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)|) := by sorry

  euclid_sentence "2.11.13"
    "Thus, the (rectangle contained) by $CF$ and $FA$, plus the (square) on $AE$, is equal to the (sum of the squares) on $BA$ and $AE$."
    (step13 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)|) := by sorry

  euclid_sentence "2.11.14"
    "Let the square on $AE$ have been subtracted from both."
    (step14 : |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|) := by sorry

  euclid_sentence "2.11.15"
    "Thus, the remaining rectangle contained by $CF$ and $FA$ is equal to the square on $AB$."
    (step15 : |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|) := by sorry

  -- @assumption ("$AF$ (is) equal to $FG$", |(a─f)| = |(f─g)|)
  euclid_sentence "2.11.16"
    "And $FK$ is the (rectangle contained) by $CF$ and $FA$. For $AF$ (is) equal to $FG$."
    (step16 : Triangle.area △ f:g:k + Triangle.area △ f:c:k = |(c─f)| * |(f─a)|) := by sorry

  euclid_sentence "2.11.17"
    "And $AD$ (is) the (square) on $AB$."
    (step17 : Triangle.area △ a:b:d + Triangle.area △ a:c:d = |(a─b)| * |(a─b)|) := by sorry

  euclid_sentence "2.11.18"
    "Thus, the (rectangle) $FK$ is equal to the (square) $AD$."
    (step18 : Triangle.area △ f:g:k + Triangle.area △ f:c:k = Triangle.area △ a:b:d + Triangle.area △ a:c:d) := by sorry

  euclid_sentence "2.11.19"
    "Let (rectangle) $AK$ be subtracted from both."
    (step19 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d) := by sorry

  euclid_sentence "2.11.20"
    "Thus, the remaining (square) $FH$ is equal to the (rectangle) $HD$."
    (step20 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d) := by sorry

  -- @assumption ("$AB$ (is) equal to $BD$", |(a─b)| = |(b─d)|)
  euclid_sentence "2.11.21"
    "And $HD$ is the (rectangle contained) by $AB$ and $BH$. For $AB$ (is) equal to $BD$."
    (step21 : Triangle.area △ h:b:d + Triangle.area △ h:k:d = |(a─b)| * |(b─h)|) := by sorry

  euclid_sentence "2.11.22"
    "And $FH$ (is) the (square) on $AH$."
    (step22 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = |(a─h)| * |(a─h)|) := by sorry

  euclid_sentence "2.11.23"
    "Thus, the rectangle contained by $AB$ and $BH$ is equal to the square on $HA$."
    (step23 : |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)|) := by sorry

  exact ⟨h, by sorry, step8⟩
  euclid_conclude_sentence "2.11.24"
    "Thus, the given straight-line $AB$ has been cut at (point) $H$ such as to make the rectangle contained by $AB$ and $BH$ equal to the square on $HA$. (Which is) the very thing it was required to do."

end Elements.Book2
