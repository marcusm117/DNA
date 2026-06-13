import SystemE
import Book.Prop31
import Book.Prop46

namespace Elements.Book2

open Elements.Book1


set_option systemE.solverTime 30 in
theorem proposition_2 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  |(a─b)| * |(b─c)| + |(b─a)| * |(a─c)| = |(a─b)| * |(a─b)| :=
by
  euclid_intros
  euclid_intro_sentence "2.2.0"
    "If a straight-line is cut at random, (then) the (sum of the) rectangle(s) contained by the whole (straight-line), and each of the pieces (of the straight-line), is equal to the square on the whole. For let the straight-line $AB$ be cut, at random, at point $C$. I say that the rectangle contained by $AB$ and $BC$, plus the rectangle contained by $BA$ and $AC$, is equal to the square on $AB$."

  euclid_apply (proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_apply (proposition_31 c a d AD) as CF
  euclid_apply (intersection_lines CF DE) as f
  euclid_sentence "2.2.1"
    "For let the square $ADEB$ be described on $AB$ [Prop.~1.46], and let $CF$ be drawn through $C$, parallel to either of $AD$ or $BE$ [Prop.~1.31]."
    (step1 : |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
             (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧
             c.onLine CF ∧ ¬(CF.intersectsLine AD) ∧
             f.onLine DE ∧ f.onLine CF ∧ between d f e) := by sorry

  euclid_sentence "2.2.2"
    "So the (square) $AE$ is equal to the (rectangles) $AF$ and $CE$."
    (step2 : Triangle.area △ d:a:b + Triangle.area △ d:b:e =
             (Triangle.area △ d:a:c + Triangle.area △ d:c:f)
           + (Triangle.area △ f:c:b + Triangle.area △ f:b:e)) := by sorry

  euclid_sentence "2.2.3"
    "And $AE$ is the square on $AB$."
    (step3 : Triangle.area △ d:a:b + Triangle.area △ d:b:e = |(a─b)| * |(a─b)|) := by sorry

  euclid_sentence "2.2.4"
    "And $AF$ (is) the rectangle contained by the (straight-lines) $BA$ and $AC$. For it is contained by $DA$ and $AC$, and $AD$ (is) equal to $AB$."
    (step4 : Triangle.area △ d:a:c + Triangle.area △ d:c:f = |(b─a)| * |(a─c)|) := by sorry

  euclid_sentence "2.2.5"
    "And $CE$ (is) the (rectangle contained) by $AB$ and $BC$. For $BE$ (is) equal to $AB$."
    (step5 : Triangle.area △ f:c:b + Triangle.area △ f:b:e = |(a─b)| * |(b─c)|) := by sorry

  euclid_sentence "2.2.6"
    "Thus, the (rectangle contained) by $BA$ and $AC$, plus the (rectangle contained) by $AB$ and $BC$, is equal to the square on $AB$."
    (step6 : |(b─a)| * |(a─c)| + |(a─b)| * |(b─c)| = |(a─b)| * |(a─b)|) := by sorry

  rw [add_comm]; exact step6
  euclid_conclude_sentence "2.2.7"
    "Thus, if a straight-line is cut at random, (then) the (sum of the) rectangle(s) contained by the whole (straight-line), and each of the pieces (of the straight-line), is equal to the square on the whole. (Which is) the very thing it was required to show."

end Elements.Book2
