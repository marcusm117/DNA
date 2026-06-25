import SystemE
import Book.Prop31
import Book.Prop46
import Book2.Prop07.step1
import Book2.Prop07.step2
import Book2.Prop07.step3
import Book2.Prop07.step4
import Book2.Prop07.step5
import Book2.Prop07.step6
import Book2.Prop07.step7
import Book2.Prop07.step8
import Book2.Prop07.step9
import Book2.Prop07.step10
import Book2.Prop07.step11
import Book2.Prop07.step12
import Book2.Prop07.step13
import Book2.Prop07.step14
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

theorem proposition_7 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| =
    2 * (|(a─b)| * |(b─c)|) + |(c─a)| * |(c─a)| :=
by
  euclid_intros
  euclid_intro_sentence "2.7.0" 
    "If a straight-line is cut at random, (then) the sum of the squares on the whole (straight-line), and one of the pieces (of the straight-line), is equal to twice the rectangle contained by the whole, and the said piece, and the square on the remaining piece. For let any straight-line $AB$ be cut, at random, at point $C$. I say that the (sum of the) squares on $AB$ and $BC$ is equal to twice the rectangle contained by $AB$ and $BC$, and the square on $CA$."

  euclid_apply (Elements.Book1.proposition_46 a b AB) as (d, e, DE, AD, BE)
  euclid_sentence "2.7.1"
    "For let the square $ADEB$ be described on $AB$ [Prop.~1.46],"
    (step1 : |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧ |(d─e)| = |(a─b)| ∧
      (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟)) := by euclid_apply (helper_2_7_step1 a b d e (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_apply (line_from_points b d) as BD
  euclid_apply (Elements.Book1.proposition_31 c a d AD) as CN
  euclid_apply (intersection_lines CN DE) as n
  euclid_apply (intersection_lines CN BD) as g
  euclid_apply (Elements.Book1.proposition_31 g a b AB) as HF
  euclid_apply (intersection_lines HF AD) as h
  euclid_apply (intersection_lines HF BE) as f
  euclid_sentence "2.7.2"
    "and let the (rest of) the figure be drawn."
    (step2 : distinctPointsOnLine b d BD ∧
      (c.onLine CN ∧ ¬(CN.intersectsLine AD)) ∧
      (g.onLine HF ∧ ¬(HF.intersectsLine AB))) := by euclid_apply (helper_2_7_step2 a b c d e n g h f AB DE AD BE BD CN HF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.7.3"
    "Therefore, since (rectangle) $AG$ is equal to (rectangle) $GE$ [Prop.~1.43], let the (square) $CF$ be added to both."
    (step3 : Triangle.area △ a:c:g + Triangle.area △ a:g:h =
      Triangle.area △ g:f:e + Triangle.area △ g:e:n) := by euclid_apply (helper_2_7_step3 a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.7.4"
    "Thus, the whole (rectangle) $AF$ is equal to the whole (rectangle) $CE$."
    (step4 : Triangle.area △ a:b:f + Triangle.area △ a:f:h =
      Triangle.area △ c:b:e + Triangle.area △ c:e:n) := by euclid_apply (helper_2_7_step4 a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.7.5"
    "Thus, (rectangle) $AF$ plus (rectangle) $CE$ is double (rectangle) $AF$."
    (step5 : (Triangle.area △ a:b:f + Triangle.area △ a:f:h) +
        (Triangle.area △ c:b:e + Triangle.area △ c:e:n) =
      (Triangle.area △ a:b:f + Triangle.area △ a:f:h) +
        (Triangle.area △ a:b:f + Triangle.area △ a:f:h)) := by euclid_apply (helper_2_7_step5 a b c e n g h f (by assumption))

  euclid_sentence "2.7.6"
    "But, (rectangle) $AF$ plus (rectangle) $CE$ is the gnomon $KLM$, and the square $CF$."
    (step6 : (Triangle.area △ a:b:f + Triangle.area △ a:f:h) +
        (Triangle.area △ c:b:e + Triangle.area △ c:e:n) =
      ((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) := by euclid_apply (helper_2_7_step6 a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.7.7"
    "Thus, the gnomon $KLM$, and the square $CF$, is double the (rectangle) $AF$."
    (step7 : ((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g) =
      (Triangle.area △ a:b:f + Triangle.area △ a:f:h) +
        (Triangle.area △ a:b:f + Triangle.area △ a:f:h)) := by euclid_apply (helper_2_7_step7 a b c e n g h f (by assumption) (by assumption))

  euclid_sentence "2.7.8"
    "But double the (rectangle) $AF$ is also twice the (rectangle contained) by $AB$ and $BC$."
    (step8 : (Triangle.area △ a:b:f + Triangle.area △ a:f:h) +
        (Triangle.area △ a:b:f + Triangle.area △ a:f:h) =
      (|(a─b)| * |(b─c)|) + (|(a─b)| * |(b─c)|)) := by euclid_apply (helper_2_7_step8 a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.7.9"
    "For $BF$ (is) equal to $BC$."
    (step9 : |(b─f)| = |(b─c)|) := by euclid_apply (helper_2_7_step9 a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.7.10"
    "Thus, the gnomon $KLM$, and the square $CF$, are equal to twice the (rectangle contained) by $AB$ and $BC$."
    (step10 : ((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g) =
      (|(a─b)| * |(b─c)|) + (|(a─b)| * |(b─c)|)) := by euclid_apply (helper_2_7_step10 a b c e n g h f AB (by assumption) (by assumption))

  euclid_sentence "2.7.11"
    "Let $DG$, which is the square on $AC$, be added to both."
    (step11 : Triangle.area △ d:h:g + Triangle.area △ d:g:n = |(a─c)| * |(a─c)|) := by euclid_apply (helper_2_7_step11 a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.7.12"
    "Thus, the gnomon $KLM$, and the squares $BG$ and $GD$, are equal to twice the rectangle contained by $AB$ and $BC$, and the square on $AC$."
    (step12 : (((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ d:h:g + Triangle.area △ d:g:n) =
      ((|(a─b)| * |(b─c)|) + (|(a─b)| * |(b─c)|)) + |(a─c)| * |(a─c)|) := by euclid_apply (helper_2_7_step12 a b c d e n g h f (by assumption) (by assumption))

  euclid_sentence "2.7.13"
    "But, the gnomon $KLM$ and the squares $BG$ and $GD$ is (equivalent to) the whole of $ADEB$ and $CF$, which are the squares on $AB$ and $BC$ (respectively)."
    (step13 : (((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ d:h:g + Triangle.area △ d:g:n) =
      |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)|) := by euclid_apply (helper_2_7_step13 a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))

  euclid_sentence "2.7.14"
    "Thus, the (sum of the) squares on $AB$ and $BC$ is equal to twice the rectangle contained by $AB$ and $BC$, and the square on $AC$."
    (step14 : |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| =
      2 * (|(a─b)| * |(b─c)|) + |(c─a)| * |(c─a)|) := by euclid_apply (helper_2_7_step14 a b c d e n g h f (by assumption) (by assumption))

  exact step14
  euclid_conclude_sentence "2.7.15"
    "Thus, if a straight-line is cut at random, (then) the sum of the squares on the whole (straight-line), and one of the pieces (of the straight-line), is equal to twice the rectangle contained by the whole, and the said piece, and the square on the remaining piece. (Which is) the very thing it was required to show."

end Elements.Book2
