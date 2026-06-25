import SystemE
import Book.Prop31
import Book.Prop46
import Book2.Prop02.step1
import Book2.Prop02.step2
import Book2.Prop02.step3
import Book2.Prop02.step4
import Book2.Prop02.step5
import Book2.Prop02.step6
import Book2.Prop02.step7
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1


theorem proposition_2 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  |(a─b)| * |(b─c)| + |(b─a)| * |(a─c)| = |(a─b)| * |(a─b)| :=
by
  euclid_intros
  euclid_intro_sentence "2.2.0"
    "If a straight-line is cut at random, (then) the (sum of the) rectangle(s) contained by the whole (straight-line), and each of the pieces (of the straight-line), is equal to the square on the whole. For let the straight-line $AB$ be cut, at random, at point $C$. I say that the rectangle contained by $AB$ and $BC$, plus the rectangle contained by $BA$ and $AC$, is equal to the square on $AB$."

  euclid_apply (Elements.Book1.proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_sentence "2.2.1"
    "For let the square $ADEB$ be described on $AB$ [Prop.~1.46],"
    (step1 : |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧ |(d─e)| = |(a─b)| ∧
      (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟)) := by euclid_apply (helper_2_2_step1 a b d e (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_apply (Elements.Book1.proposition_31 c a d AD) as CF
  euclid_apply (intersection_lines CF DE) as f
  euclid_sentence "2.2.2"
    "and let $CF$ be drawn through $C$, parallel to either of $AD$ or $BE$ [Prop.~1.31]."
    (step2 : c.onLine CF ∧ ¬(CF.intersectsLine AD)) := by euclid_apply (helper_2_2_step2 c CF AD (by assumption) (by assumption))

  euclid_sentence "2.2.3"
    "So the (square) $AE$ is equal to the (rectangles) $AF$ and $CE$."
    (step3 : Triangle.area △ a:d:e + Triangle.area △ a:b:e =
      (Triangle.area △ a:c:f + Triangle.area △ a:d:f)
    + (Triangle.area △ c:b:e + Triangle.area △ c:f:e)) := by euclid_apply (helper_2_2_step3 a b c d e f AB DE AD BE CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.2.4"
    "And $AE$ is the square on $AB$."
    (step4 : Triangle.area △ a:d:e + Triangle.area △ a:b:e = |(a─b)| * |(a─b)|) := by euclid_apply (helper_2_2_step4 a b d e AB DE AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.2.5"
    "And $AF$ (is) the rectangle contained by the (straight-lines) $BA$ and $AC$. For it is contained by $DA$ and $AC$, and $AD$ (is) equal to $AB$."
    (step5 : Triangle.area △ a:c:f + Triangle.area △ a:d:f = |(b─a)| * |(a─c)|) := by euclid_apply (helper_2_2_step5 a b c d e f AB DE AD BE CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.2.6"
    "And $CE$ (is) the (rectangle contained) by $AB$ and $BC$. For $BE$ (is) equal to $AB$."
    (step6 : Triangle.area △ c:b:e + Triangle.area △ c:f:e = |(a─b)| * |(b─c)|) := by euclid_apply (helper_2_2_step6 a b c d e f AB DE AD BE CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.2.7"
    "Thus, the (rectangle contained) by $BA$ and $AC$, plus the (rectangle contained) by $AB$ and $BC$, is equal to the square on $AB$."
    (step7 : |(b─a)| * |(a─c)| + |(a─b)| * |(b─c)| = |(a─b)| * |(a─b)|) := by euclid_apply (helper_2_2_step7 a b c d e f (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_finish
  euclid_conclude_sentence "2.2.8"
    "Thus, if a straight-line is cut at random, (then) the (sum of the) rectangle(s) contained by the whole (straight-line), and each of the pieces (of the straight-line), is equal to the square on the whole. (Which is) the very thing it was required to show."

end Elements.Book2
