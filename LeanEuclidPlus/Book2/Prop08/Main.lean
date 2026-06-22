import SystemE
import Book.Prop03
import Book.Prop31
import Book.Prop46

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_8 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  4 * (|(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| =
    (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|) := by
  euclid_intros
  euclid_intro_sentence "2.8.0"
    "If a straight-line is cut at random, (then) four times the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), plus the square on the remaining piece, is equal to the square described on the whole and the former piece, as on one (complete straight-line). For let any straight-line $AB$ be cut, at random, at point $C$. I say that four times the rectangle contained by $AB$ and $BC$, plus the square on $AC$, is equal to the square described on $AB$ and $BC$, as on one (complete straight-line)."

  euclid_apply (extend_point_longer AB a b (c─b)) as d'
  euclid_apply (proposition_3 b d' c b AB AB) as d
  euclid_sentence "2.8.1"
    "For let $BD$ be produced in a straight-line [with the straight-line $AB$], and let $BD$ be made equal to $CB$ [Prop.~1.3],"
    (step1 : True) := by sorry

  euclid_apply (proposition_46 a d AB) as (e, f, EF, AE, DF)
  euclid_sentence "2.8.2"
    "and let the square $AEFD$ be described on $AD$ [Prop.~1.46],"
    (step2 : True) := by sorry

  euclid_apply (line_from_points e d) as ED
  euclid_apply (proposition_31 c a e AE) as CH
  euclid_apply (proposition_31 b a e AE) as BL
  euclid_apply (intersection_lines BL ED) as k
  euclid_apply (intersection_lines CH ED) as q
  euclid_apply (proposition_31 k a d AB) as MN
  euclid_apply (proposition_31 q a d AB) as OP
  euclid_apply (intersection_lines CH MN) as g
  euclid_apply (intersection_lines CH EF) as h
  euclid_apply (intersection_lines BL EF) as l
  euclid_apply (intersection_lines AE MN) as m
  euclid_apply (intersection_lines DF MN) as n
  euclid_apply (intersection_lines AE OP) as o
  euclid_apply (intersection_lines DF OP) as p
  euclid_apply (intersection_lines BL OP) as r
  euclid_sentence "2.8.3"
    "and let the (rest of the) figure be drawn double."
    (step3 : True) := by sorry

  euclid_sentence "2.8.4"
    "Therefore, since $CB$ is equal to $BD$, but $CB$ is equal to $GK$ [Prop.~1.34], and $BD$ to $KN$ [Prop.~1.34], $GK$ is thus also equal to $KN$."
    (step4 : True) := by sorry

  euclid_sentence "2.8.5"
    "So, for the same (reasons), $QR$ is equal to $RP$."
    (step5 : True) := by sorry

  euclid_sentence "2.8.6"
    "And since $BC$ is equal to $BD$, and $GK$ to $KN$, (square) $CK$ is thus also equal to (square) $KD$,"
    (step6 : True) := by sorry

  euclid_sentence "2.8.7"
    "and (square) $GR$ to (square) $RN$ [Prop.~1.36]."
    (step7 : True) := by sorry

  euclid_sentence "2.8.8"
    "But, (square) $CK$ is equal to (square) $RN$. For (they are) complements in the parallelogram $CP$ [Prop.~1.43]."
    (step8 : True) := by sorry

  euclid_sentence "2.8.9"
    "Thus, (square) $KD$ is also equal to (square) $GR$."
    (step9 : True) := by sorry

  euclid_sentence "2.8.10"
    "Thus, the four (squares) $DK$, $CK$, $GR$, and $RN$ are equal to one another."
    (step10 : True) := by sorry

  euclid_sentence "2.8.11"
    "Thus, the four (taken together) are quadruple (square) $CK$."
    (step11 : True) := by sorry

  euclid_sentence "2.8.12"
    "Again, since $CB$ is equal to $BD$, but $BD$ (is) equal to $BK$---that is to say, $CG$---and $CB$ is equal to $GK$---that is to say, $GQ$---$CG$ is thus also equal to $GQ$."
    (step12 : True) := by sorry

  euclid_sentence "2.8.13"
    "And since $CG$ is equal to $GQ$, and $QR$ to $RP$, (rectangle) $AG$ is also equal to (rectangle) $MQ$,"
    (step13 : True) := by sorry

  euclid_sentence "2.8.14"
    "and (rectangle) $QL$ to (rectangle) $RF$ [Prop.~1.36]."
    (step14 : True) := by sorry

  euclid_sentence "2.8.15"
    "But, (rectangle) $MQ$ is equal to (rectangle) $QL$. For (they are) complements in the parallelogram $ML$ [Prop.~1.43]."
    (step15 : True) := by sorry

  euclid_sentence "2.8.16"
    "Thus, (rectangle) $AG$ is also equal to (rectangle) $RF$."
    (step16 : True) := by sorry

  euclid_sentence "2.8.17"
    "Thus, the four (rectangles) $AG$, $MQ$, $QL$, and $RF$ are equal to one another."
    (step17 : True) := by sorry

  euclid_sentence "2.8.18"
    "Thus, the four (taken together) are quadruple (rectangle) $AG$."
    (step18 : True) := by sorry

  euclid_sentence "2.8.19"
    "And it was also shown that the four (squares) $CK$, $KD$, $GR$, and $RN$ (taken together are) quadruple (square) $CK$."
    (step19 : True) := by sorry

  euclid_sentence "2.8.20"
    "Thus, the eight (figures taken together), which comprise the gnomon $STU$, are quadruple (rectangle) $AK$."
    (step20 : True) := by sorry

  euclid_sentence "2.8.21"
    "And since $AK$ is the (rectangle contained) by $AB$ and $BD$, for $BK$ (is) equal to $BD$, four times the (rectangle contained) by $AB$ and $BD$ is quadruple (rectangle) $AK$."
    (step21 : True) := by sorry

  euclid_sentence "2.8.22"
    "But the gnomon $STU$ was also shown (to be equal to) quadruple (rectangle) $AK$."
    (step22 : True) := by sorry

  euclid_sentence "2.8.23"
    "Thus, four times the (rectangle contained) by $AB$ and $BD$ is equal to the gnomon $STU$."
    (step23 : True) := by sorry

  euclid_sentence "2.8.24"
    "Let $OH$, which is equal to the square on $AC$, be added to both."
    (step24 : True) := by sorry

  euclid_sentence "2.8.25"
    "Thus, four times the rectangle contained by $AB$ and $BD$, plus the square on $AC$, is equal to the gnomon $STU$, and the (square) $OH$."
    (step25 : True) := by sorry

  euclid_sentence "2.8.26"
    "But, the gnomon $STU$ and the (square) $OH$ is (equivalent to) the whole square $AEFD$, which is on $AD$."
    (step26 : True) := by sorry

  euclid_sentence "2.8.27"
    "Thus, four times the (rectangle contained) by $AB$ and $BD$, plus the (square) on $AC$, is equal to the square on $AD$."
    (step27 : True) := by sorry

  euclid_sentence "2.8.28"
    "And $BD$ (is) equal to $BC$."
    (step28 : True) := by sorry

  euclid_sentence "2.8.29"
    "Thus, four times the rectangle contained by $AB$ and $BC$, plus the square on $AC$, is equal to the (square) on $AD$, that is to say the square described on $AB$ and $BC$, as on one (complete straight-line)."
    (step29 : True) := by sorry

  exact step29
  euclid_conclude_sentence "2.8.30"
    "Thus, if a straight-line is cut at random, (then) four times the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), plus the square on the remaining piece, is equal to the square described on the whole and the former piece, as on one (complete straight-line). (Which is) the very thing it was required to show."

end Elements.Book2
