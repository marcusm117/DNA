import SystemE
import Book.Prop03
import Book.Prop31
import Book.Prop46
import Book2.Prop08.step1
import Book2.Prop08.step2
import Book2.Prop08.step3
import Book2.Prop08.step4
import Book2.Prop08.step5
import Book2.Prop08.step6
import Book2.Prop08.step7
import Book2.Prop08.step8
import Book2.Prop08.step9
import Book2.Prop08.step10
import Book2.Prop08.step11
import Book2.Prop08.step12
import Book2.Prop08.step13
import Book2.Prop08.step14
import Book2.Prop08.step15
import Book2.Prop08.step16
import Book2.Prop08.step17
import Book2.Prop08.step18
import Book2.Prop08.step19
import Book2.Prop08.step20
import Book2.Prop08.step21
import Book2.Prop08.step22
import Book2.Prop08.step23
import Book2.Prop08.step24
import Book2.Prop08.step25
import Book2.Prop08.step26
import Book2.Prop08.step27
import Book2.Prop08.step28
import Book2.Prop08.step29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

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
    (step1 : between a b d ∧ |(b─d)| = |(c─b)|) := by euclid_apply (helper_2_8_step1 a b c d d' AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between a b d'; assumption)) (by euclid_assumption "" (show between b d d'; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)))

  euclid_apply (proposition_46 a d AB) as (e, f, EF, AE, DF)
  euclid_sentence "2.8.2"
    "and let the square $AEFD$ be described on $AD$ [Prop.~1.46],"
    (step2 : |(e─f)| = |(a─d)| ∧ |(a─e)| = |(a─d)| ∧ |(d─f)| = |(a─d)| ∧
      (∠ d:a:e = ∟) ∧ (∠ a:e:f = ∟) ∧ (∠ a:d:f = ∟) ∧ (∠ d:f:e = ∟)) := by euclid_apply (helper_2_8_step2 a d e f (by euclid_assumption "" (show |(e─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show ∠ d:f:e = ∟; assumption)))

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
    (step3 : c.onLine CH ∧ ¬(CH.intersectsLine AE) ∧ b.onLine BL ∧ ¬(BL.intersectsLine AE) ∧
      k.onLine MN ∧ ¬(MN.intersectsLine AB) ∧ q.onLine OP ∧ ¬(OP.intersectsLine AB)) := by euclid_apply (helper_2_8_step3 b c k q AB AE BL CH MN OP (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)))

  euclid_sentence "2.8.4"
    "Therefore, since $CB$ is equal to $BD$, but $CB$ is equal to $GK$ [Prop.~1.34], and $BD$ to $KN$ [Prop.~1.34], $GK$ is thus also equal to $KN$."
    (step4 : |(g─k)| = |(k─n)|) := by euclid_apply (helper_2_8_step4 a b c d e f g k n AB AE BL CH DF ED MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)))

  euclid_sentence "2.8.5"
    "So, for the same (reasons), $QR$ is equal to $RP$."
    (step5 : |(q─r)| = |(r─p)|) := by euclid_apply (helper_2_8_step5 a b c d e f q r p AB AE BL CH DF ED OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show r.onLine BL; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show p.onLine OP; assumption)) (by euclid_assumption "" (show p.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)))

  euclid_sentence "2.8.6"
    "And since $BC$ is equal to $BD$, and $GK$ to $KN$, (square) $CK$ is thus also equal to (square) $KD$,"
    (step6 : Triangle.area △ g:c:b + Triangle.area △ g:b:k =
      Triangle.area △ k:b:d + Triangle.area △ k:d:n) := by euclid_apply (helper_2_8_step6 a b c d e f g k n AB AE BL CH DF ED MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(g─k)| = |(k─n)|; assumption)))

  euclid_sentence "2.8.7"
    "and (square) $GR$ to (square) $RN$ [Prop.~1.36]."
    (step7 : Triangle.area △ g:k:r + Triangle.area △ g:r:q =
      Triangle.area △ k:n:p + Triangle.area △ k:p:r) := by euclid_apply (helper_2_8_step7 a b c d e f g k n q r p AB AE BL CH DF ED MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show r.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show p.onLine OP; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show p.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(g─k)| = |(k─n)|; assumption)) (by euclid_assumption "" (show |(q─r)| = |(r─p)|; assumption)) (by euclid_assumption "" (show Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:b:d + Triangle.area △ k:d:n; assumption)))

  euclid_sentence "2.8.8"
    "But, (square) $CK$ is equal to (square) $RN$. For (they are) complements in the parallelogram $CP$ [Prop.~1.43]."
    (step8 : Triangle.area △ g:c:b + Triangle.area △ g:b:k =
      Triangle.area △ k:n:p + Triangle.area △ k:p:r) := by euclid_apply (helper_2_8_step8 a b c d e f g k n q r p AB AE BL CH DF ED MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show r.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show p.onLine OP; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show p.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(g─k)| = |(k─n)|; assumption)) (by euclid_assumption "" (show |(q─r)| = |(r─p)|; assumption)) (by euclid_assumption "" (show Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:b:d + Triangle.area △ k:d:n; assumption)))

  euclid_sentence "2.8.9"
    "Thus, (square) $KD$ is also equal to (square) $GR$."
    (step9 : Triangle.area △ k:b:d + Triangle.area △ k:d:n =
      Triangle.area △ g:k:r + Triangle.area △ g:r:q) := by euclid_apply (helper_2_8_step9 g c b k d n q r p (by euclid_assumption "" (show Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:b:d + Triangle.area △ k:d:n; assumption)) (by euclid_assumption "" (show Triangle.area △ g:k:r + Triangle.area △ g:r:q = Triangle.area △ k:n:p + Triangle.area △ k:p:r; assumption)) (by euclid_assumption "" (show Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:n:p + Triangle.area △ k:p:r; assumption)))

  euclid_sentence "2.8.10"
    "Thus, the four (squares) $DK$, $CK$, $GR$, and $RN$ are equal to one another."
    (step10 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k =
        Triangle.area △ k:b:d + Triangle.area △ k:d:n) ∧
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n =
        Triangle.area △ g:k:r + Triangle.area △ g:r:q) ∧
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q =
        Triangle.area △ k:n:p + Triangle.area △ k:p:r)) := by euclid_apply (helper_2_8_step10 g c b k d n q r p (by euclid_assumption "" (show Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:b:d + Triangle.area △ k:d:n; assumption)) (by euclid_assumption "" (show Triangle.area △ k:b:d + Triangle.area △ k:d:n = Triangle.area △ g:k:r + Triangle.area △ g:r:q; assumption)) (by euclid_assumption "" (show Triangle.area △ g:k:r + Triangle.area △ g:r:q = Triangle.area △ k:n:p + Triangle.area △ k:p:r; assumption)))

  euclid_sentence "2.8.11"
    "Thus, the four (taken together) are quadruple (square) $CK$."
    (step11 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) =
      4 * (Triangle.area △ g:c:b + Triangle.area △ g:b:k)) := by euclid_apply (helper_2_8_step11 g c b k d n q r p (by euclid_assumption "" (show (Triangle.area △ g:c:b + Triangle.area △ g:b:k = Triangle.area △ k:b:d + Triangle.area △ k:d:n) ∧ (Triangle.area △ k:b:d + Triangle.area △ k:d:n = Triangle.area △ g:k:r + Triangle.area △ g:r:q) ∧ (Triangle.area △ g:k:r + Triangle.area △ g:r:q = Triangle.area △ k:n:p + Triangle.area △ k:p:r); assumption)))

  euclid_sentence "2.8.12"
    "Again, since $CB$ is equal to $BD$, but $BD$ (is) equal to $BK$---that is to say, $CG$---and $CB$ is equal to $GK$---that is to say, $GQ$---$CG$ is thus also equal to $GQ$."
    (step12 : |(c─g)| = |(g─q)|) := by euclid_apply (helper_2_8_step12 a b c d e f g k q n AB AE BL CH DF ED MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)))

  euclid_sentence "2.8.13"
    "And since $CG$ is equal to $GQ$, and $QR$ to $RP$, (rectangle) $AG$ is also equal to (rectangle) $MQ$,"
    (step13 : Triangle.area △ a:c:g + Triangle.area △ a:g:m =
      Triangle.area △ m:g:q + Triangle.area △ m:q:o) := by euclid_apply (helper_2_8_step13 a b c d e g k m o q AB AE BL CH ED MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show m.onLine AE; assumption)) (by euclid_assumption "" (show o.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show o.onLine OP; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show |(c─g)| = |(g─q)|; assumption)))

  euclid_sentence "2.8.14"
    "and (rectangle) $QL$ to (rectangle) $RF$ [Prop.~1.36]."
    (step14 : Triangle.area △ q:r:l + Triangle.area △ q:l:h =
      Triangle.area △ r:p:f + Triangle.area △ r:f:l) := by euclid_apply (helper_2_8_step14 a b c d e f g k h l m n o q r p AB AE BL CH DF ED EF MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show r.onLine BL; assumption)) (by euclid_assumption "" (show l.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show p.onLine OP; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show l.onLine EF; assumption)) (by euclid_assumption "" (show p.onLine DF; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(q─r)| = |(r─p)|; assumption)))

  euclid_sentence "2.8.15"
    "But, (rectangle) $MQ$ is equal to (rectangle) $QL$. For (they are) complements in the parallelogram $ML$ [Prop.~1.43]."
    (step15 : Triangle.area △ m:g:q + Triangle.area △ m:q:o =
      Triangle.area △ q:r:l + Triangle.area △ q:l:h) := by euclid_apply (helper_2_8_step15 a b c d e g k h l m o q r AB AE BL CH ED EF MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show m.onLine AE; assumption)) (by euclid_assumption "" (show o.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show l.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show r.onLine BL; assumption)) (by euclid_assumption "" (show l.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show o.onLine OP; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)))

  euclid_sentence "2.8.16"
    "Thus, (rectangle) $AG$ is also equal to (rectangle) $RF$."
    (step16 : Triangle.area △ a:c:g + Triangle.area △ a:g:m =
      Triangle.area △ r:p:f + Triangle.area △ r:f:l) := by euclid_apply (helper_2_8_step16 a c g m o q r l h p f (by euclid_assumption "" (show Triangle.area △ a:c:g + Triangle.area △ a:g:m = Triangle.area △ m:g:q + Triangle.area △ m:q:o; assumption)) (by euclid_assumption "" (show Triangle.area △ q:r:l + Triangle.area △ q:l:h = Triangle.area △ r:p:f + Triangle.area △ r:f:l; assumption)) (by euclid_assumption "" (show Triangle.area △ m:g:q + Triangle.area △ m:q:o = Triangle.area △ q:r:l + Triangle.area △ q:l:h; assumption)))

  euclid_sentence "2.8.17"
    "Thus, the four (rectangles) $AG$, $MQ$, $QL$, and $RF$ are equal to one another."
    (step17 : (Triangle.area △ a:c:g + Triangle.area △ a:g:m =
        Triangle.area △ m:g:q + Triangle.area △ m:q:o) ∧
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o =
        Triangle.area △ q:r:l + Triangle.area △ q:l:h) ∧
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h =
        Triangle.area △ r:p:f + Triangle.area △ r:f:l)) := by euclid_apply (helper_2_8_step17 a c g m o q r l h p f (by euclid_assumption "" (show Triangle.area △ a:c:g + Triangle.area △ a:g:m = Triangle.area △ m:g:q + Triangle.area △ m:q:o; assumption)) (by euclid_assumption "" (show Triangle.area △ m:g:q + Triangle.area △ m:q:o = Triangle.area △ q:r:l + Triangle.area △ q:l:h; assumption)) (by euclid_assumption "" (show Triangle.area △ q:r:l + Triangle.area △ q:l:h = Triangle.area △ r:p:f + Triangle.area △ r:f:l; assumption)))

  euclid_sentence "2.8.18"
    "Thus, the four (taken together) are quadruple (rectangle) $AG$."
    (step18 : (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) =
      4 * (Triangle.area △ a:c:g + Triangle.area △ a:g:m)) := by euclid_apply (helper_2_8_step18 a c g m o q r l h p f (by euclid_assumption "" (show (Triangle.area △ a:c:g + Triangle.area △ a:g:m = Triangle.area △ m:g:q + Triangle.area △ m:q:o) ∧ (Triangle.area △ m:g:q + Triangle.area △ m:q:o = Triangle.area △ q:r:l + Triangle.area △ q:l:h) ∧ (Triangle.area △ q:r:l + Triangle.area △ q:l:h = Triangle.area △ r:p:f + Triangle.area △ r:f:l); assumption)))

  euclid_sentence "2.8.19"
    "And it was also shown that the four (squares) $CK$, $KD$, $GR$, and $RN$ (taken together are) quadruple (square) $CK$."
    (step19 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) =
      4 * (Triangle.area △ g:c:b + Triangle.area △ g:b:k)) := by euclid_apply (helper_2_8_step19 g c b k d n q r p (by euclid_assumption "" (show (Triangle.area △ g:c:b + Triangle.area △ g:b:k) + (Triangle.area △ k:b:d + Triangle.area △ k:d:n) + (Triangle.area △ g:k:r + Triangle.area △ g:r:q) + (Triangle.area △ k:n:p + Triangle.area △ k:p:r) = 4 * (Triangle.area △ g:c:b + Triangle.area △ g:b:k); assumption)))

  euclid_sentence "2.8.20"
    "Thus, the eight (figures taken together), which comprise the gnomon $STU$, are quadruple (rectangle) $AK$."
    (step20 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) =
      4 * (Triangle.area △ a:b:k + Triangle.area △ a:k:m)) := by euclid_apply (helper_2_8_step20 a b c d e f g k n m o q r l h p AB AE BL CH DF ED MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show m.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show (Triangle.area △ g:c:b + Triangle.area △ g:b:k) + (Triangle.area △ k:b:d + Triangle.area △ k:d:n) + (Triangle.area △ g:k:r + Triangle.area △ g:r:q) + (Triangle.area △ k:n:p + Triangle.area △ k:p:r) = 4 * (Triangle.area △ g:c:b + Triangle.area △ g:b:k); assumption)) (by euclid_assumption "" (show (Triangle.area △ a:c:g + Triangle.area △ a:g:m) + (Triangle.area △ m:g:q + Triangle.area △ m:q:o) + (Triangle.area △ q:r:l + Triangle.area △ q:l:h) + (Triangle.area △ r:p:f + Triangle.area △ r:f:l) = 4 * (Triangle.area △ a:c:g + Triangle.area △ a:g:m); assumption)))

  euclid_sentence "2.8.21"
    "And since $AK$ is the (rectangle contained) by $AB$ and $BD$, for $BK$ (is) equal to $BD$, four times the (rectangle contained) by $AB$ and $BD$ is quadruple (rectangle) $AK$."
    (step21 : Triangle.area △ a:b:k + Triangle.area △ a:k:m = |(a─b)| * |(b─d)|) := by euclid_apply (helper_2_8_step21 a b c d e g k m q AB AE BL CH ED MN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show m.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)))

  euclid_sentence "2.8.22"
    "But the gnomon $STU$ was also shown (to be equal to) quadruple (rectangle) $AK$."
    (step22 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) =
      4 * (Triangle.area △ a:b:k + Triangle.area △ a:k:m)) := by euclid_apply (helper_2_8_step22 a b c d e f g k n m o q r l h p (by euclid_assumption "" (show (Triangle.area △ g:c:b + Triangle.area △ g:b:k) + (Triangle.area △ k:b:d + Triangle.area △ k:d:n) + (Triangle.area △ g:k:r + Triangle.area △ g:r:q) + (Triangle.area △ k:n:p + Triangle.area △ k:p:r) + (Triangle.area △ a:c:g + Triangle.area △ a:g:m) + (Triangle.area △ m:g:q + Triangle.area △ m:q:o) + (Triangle.area △ q:r:l + Triangle.area △ q:l:h) + (Triangle.area △ r:p:f + Triangle.area △ r:f:l) = 4 * (Triangle.area △ a:b:k + Triangle.area △ a:k:m); assumption)))

  euclid_sentence "2.8.23"
    "Thus, four times the (rectangle contained) by $AB$ and $BD$ is equal to the gnomon $STU$."
    (step23 : 4 * (|(a─b)| * |(b─d)|) =
      (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l)) := by euclid_apply (helper_2_8_step23 a b c d e f g k n m o q r l h p (by euclid_assumption "" (show (Triangle.area △ g:c:b + Triangle.area △ g:b:k) + (Triangle.area △ k:b:d + Triangle.area △ k:d:n) + (Triangle.area △ g:k:r + Triangle.area △ g:r:q) + (Triangle.area △ k:n:p + Triangle.area △ k:p:r) + (Triangle.area △ a:c:g + Triangle.area △ a:g:m) + (Triangle.area △ m:g:q + Triangle.area △ m:q:o) + (Triangle.area △ q:r:l + Triangle.area △ q:l:h) + (Triangle.area △ r:p:f + Triangle.area △ r:f:l) = 4 * (Triangle.area △ a:b:k + Triangle.area △ a:k:m); assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:k + Triangle.area △ a:k:m = |(a─b)| * |(b─d)|; assumption)))

  euclid_sentence "2.8.24"
    "Let $OH$, which is equal to the square on $AC$, be added to both."
    (step24 : Triangle.area △ o:q:h + Triangle.area △ o:h:e = |(a─c)| * |(a─c)|) := by euclid_apply (helper_2_8_step24 a b c d e f g h k m o q AB AE BL CH DF ED EF MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show m.onLine AE; assumption)) (by euclid_assumption "" (show o.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(e─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show o.onLine OP; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:e:f = ∟; assumption)))

  euclid_sentence "2.8.25"
    "Thus, four times the rectangle contained by $AB$ and $BD$, plus the square on $AC$, is equal to the gnomon $STU$, and the (square) $OH$."
    (step25 : 4 * (|(a─b)| * |(b─d)|) + |(a─c)| * |(a─c)| =
      (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) +
      (Triangle.area △ o:q:h + Triangle.area △ o:h:e)) := by euclid_apply (helper_2_8_step25 a b c d e f g k n m o q r l h p (by euclid_assumption "" (show 4 * (|(a─b)| * |(b─d)|) = (Triangle.area △ g:c:b + Triangle.area △ g:b:k) + (Triangle.area △ k:b:d + Triangle.area △ k:d:n) + (Triangle.area △ g:k:r + Triangle.area △ g:r:q) + (Triangle.area △ k:n:p + Triangle.area △ k:p:r) + (Triangle.area △ a:c:g + Triangle.area △ a:g:m) + (Triangle.area △ m:g:q + Triangle.area △ m:q:o) + (Triangle.area △ q:r:l + Triangle.area △ q:l:h) + (Triangle.area △ r:p:f + Triangle.area △ r:f:l); assumption)) (by euclid_assumption "" (show Triangle.area △ o:q:h + Triangle.area △ o:h:e = |(a─c)| * |(a─c)|; assumption)))

  euclid_sentence "2.8.26"
    "But, the gnomon $STU$ and the (square) $OH$ is (equivalent to) the whole square $AEFD$, which is on $AD$."
    (step26 : (Triangle.area △ g:c:b + Triangle.area △ g:b:k) +
      (Triangle.area △ k:b:d + Triangle.area △ k:d:n) +
      (Triangle.area △ g:k:r + Triangle.area △ g:r:q) +
      (Triangle.area △ k:n:p + Triangle.area △ k:p:r) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:m) +
      (Triangle.area △ m:g:q + Triangle.area △ m:q:o) +
      (Triangle.area △ q:r:l + Triangle.area △ q:l:h) +
      (Triangle.area △ r:p:f + Triangle.area △ r:f:l) +
      (Triangle.area △ o:q:h + Triangle.area △ o:h:e) =
      Triangle.area △ a:e:f + Triangle.area △ a:f:d) := by euclid_apply (helper_2_8_step26 a b c d e f g k n m o q r l h p AB AE DF EF ED CH BL MN OP (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show m.onLine AE; assumption)) (by euclid_assumption "" (show o.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show n.onLine DF; assumption)) (by euclid_assumption "" (show p.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show l.onLine EF; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show k.onLine ED; assumption)) (by euclid_assumption "" (show q.onLine ED; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show g.onLine CH; assumption)) (by euclid_assumption "" (show q.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show b.onLine BL; assumption)) (by euclid_assumption "" (show k.onLine BL; assumption)) (by euclid_assumption "" (show r.onLine BL; assumption)) (by euclid_assumption "" (show l.onLine BL; assumption)) (by euclid_assumption "" (show g.onLine MN; assumption)) (by euclid_assumption "" (show k.onLine MN; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show o.onLine OP; assumption)) (by euclid_assumption "" (show q.onLine OP; assumption)) (by euclid_assumption "" (show r.onLine OP; assumption)) (by euclid_assumption "" (show p.onLine OP; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(BL.intersectsLine AE); assumption)) (by euclid_assumption "" (show ¬(MN.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(OP.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:e:f = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:f = ∟; assumption)) (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)))

  euclid_sentence "2.8.27"
    "Thus, four times the (rectangle contained) by $AB$ and $BD$, plus the (square) on $AC$, is equal to the square on $AD$."
    (step27 : 4 * (|(a─b)| * |(b─d)|) + |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)|) := by euclid_apply (helper_2_8_step27 a b c d e f g k n m o q r l h p AB AE DF EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show |(a─e)| = |(a─d)|; assumption)) (by euclid_assumption "" (show |(d─f)| = |(a─d)|; assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ a:e:f = ∟; assumption)) (by euclid_assumption "" (show 4 * (|(a─b)| * |(b─d)|) + |(a─c)| * |(a─c)| = (Triangle.area △ g:c:b + Triangle.area △ g:b:k) + (Triangle.area △ k:b:d + Triangle.area △ k:d:n) + (Triangle.area △ g:k:r + Triangle.area △ g:r:q) + (Triangle.area △ k:n:p + Triangle.area △ k:p:r) + (Triangle.area △ a:c:g + Triangle.area △ a:g:m) + (Triangle.area △ m:g:q + Triangle.area △ m:q:o) + (Triangle.area △ q:r:l + Triangle.area △ q:l:h) + (Triangle.area △ r:p:f + Triangle.area △ r:f:l) + (Triangle.area △ o:q:h + Triangle.area △ o:h:e); assumption)) (by euclid_assumption "" (show (Triangle.area △ g:c:b + Triangle.area △ g:b:k) + (Triangle.area △ k:b:d + Triangle.area △ k:d:n) + (Triangle.area △ g:k:r + Triangle.area △ g:r:q) + (Triangle.area △ k:n:p + Triangle.area △ k:p:r) + (Triangle.area △ a:c:g + Triangle.area △ a:g:m) + (Triangle.area △ m:g:q + Triangle.area △ m:q:o) + (Triangle.area △ q:r:l + Triangle.area △ q:l:h) + (Triangle.area △ r:p:f + Triangle.area △ r:f:l) + (Triangle.area △ o:q:h + Triangle.area △ o:h:e) = Triangle.area △ a:e:f + Triangle.area △ a:f:d; assumption)))

  euclid_sentence "2.8.28"
    "And $BD$ (is) equal to $BC$."
    (step28 : |(b─d)| = |(b─c)|) := by euclid_apply (helper_2_8_step28 b c d (by euclid_assumption "" (show |(b─d)| = |(c─b)|; assumption)))

  euclid_sentence "2.8.29"
    "Thus, four times the rectangle contained by $AB$ and $BC$, plus the square on $AC$, is equal to the (square) on $AD$, that is to say the square described on $AB$ and $BC$, as on one (complete straight-line)."
    (step29 : 4 * (|(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| =
      (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|)) := by euclid_apply (helper_2_8_step29 a b c d (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show 4 * (|(a─b)| * |(b─d)|) + |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)|; assumption)) (by euclid_assumption "" (show |(b─d)| = |(b─c)|; assumption)))

  exact step29
  euclid_conclude_sentence "2.8.30"
    "Thus, if a straight-line is cut at random, (then) four times the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), plus the square on the remaining piece, is equal to the square described on the whole and the former piece, as on one (complete straight-line). (Which is) the very thing it was required to show."

end Elements.Book2
