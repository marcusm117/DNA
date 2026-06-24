import SystemE
import Book.Prop03
import Book.Prop11
import Book.Prop31
import Book2.Prop09.step1
import Book2.Prop09.step2
import Book2.Prop09.step3
import Book2.Prop09.step4
import Book2.Prop09.step5
import Book2.Prop09.step6
import Book2.Prop09.step7
import Book2.Prop09.step8
import Book2.Prop09.step9
import Book2.Prop09.step10
import Book2.Prop09.step11
import Book2.Prop09.step12
import Book2.Prop09.step13
import Book2.Prop09.step14
import Book2.Prop09.step15
import Book2.Prop09.step16
import Book2.Prop09.step17
import Book2.Prop09.step18
import Book2.Prop09.step19
import Book2.Prop09.step20
import Book2.Prop09.step21
import Book2.Prop09.step23
import Book2.Prop09.step24
import Book2.Prop09.step25
import Book2.Prop09.step26
import Book2.Prop09.step27
import Book2.Prop09.step28
import Book2.Prop09.step29
import Book2.Prop09.step30
import Book2.Prop09.step31
import Book2.Prop09.step32
import Book2.Prop09.step34
import Book2.Prop09.step35
import Book2.Prop09.step37
import Book2.Prop09.step38
import Book2.Prop09.step39
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

theorem proposition_9 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c b ∧ |(a─c)| = |(c─b)| ∧ between c d b →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
    2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  euclid_intros
  euclid_intro_sentence "2.9.0"
    "If a straight-line is cut into equal and unequal (pieces, then) the (sum of the) squares on the unequal pieces of the whole (straight-line) is double the (sum of the) square on half (the straight-line) and (the square) on the (difference) between the (equal and unequal) pieces. For let any straight-line $AB$ be cut---equally at $C$, and unequally at $D$. I say that the (sum of the) squares on $AD$ and $DB$ is double the (sum of the squares) on $AC$ and $CD$."

  euclid_apply (proposition_11 a b c AB) as e0
  euclid_apply (line_from_points c e0) as CE
  euclid_apply (line_from_points a c) as AC'
  euclid_apply (extend_point_longer CE c e0 (a─c)) as e1
  euclid_apply (proposition_3 c e1 a c CE AC') as e
  euclid_sentence "2.9.1"
    "For let $CE$ be drawn from (point) $C$, at right-angles to $AB$ [Prop.~1.11],"
    (step1 : ∠ a:c:e = ∟) := by euclid_apply (helper_2_9_step1 a b c e e0 e1 AC' CE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.2"
    "and let it be made equal to each of $AC$ and $CB$ [Prop.~1.3],"
    (step2 : |(c─e)| = |(a─c)| ∧ |(c─e)| = |(c─b)|) := by euclid_apply (helper_2_9_step2 a b c e (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_sentence "2.9.3"
    "and let $EA$ and $EB$ be joined."
    (step3 : distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB) := by euclid_apply (helper_2_9_step3 a b c e e0 e1 AB CE EA EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_apply (proposition_31 d c e0 CE) as DF
  euclid_apply (intersection_lines DF EB) as f
  euclid_sentence "2.9.4"
    "And let $DF$ be drawn through (point) $D$, parallel to $EC$ [Prop.~1.31],"
    (step4 : d.onLine DF ∧ ¬(DF.intersectsLine CE)) := by euclid_apply (helper_2_9_step4 d DF CE (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_apply (proposition_31 f a b AB) as FG
  euclid_apply (intersection_lines FG CE) as g
  euclid_sentence "2.9.5"
    "and (let) $FG$ (be drawn) through (point) $F$, (parallel) to $AB$ [Prop.~1.31]."
    (step5 : f.onLine FG ∧ ¬(FG.intersectsLine AB)) := by euclid_apply (helper_2_9_step5 f FG AB (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_apply (line_from_points a f) as AF
  euclid_sentence "2.9.6"
    "And let $AF$ be joined."
    (step6 : distinctPointsOnLine a f AF) := by euclid_apply (helper_2_9_step6 a b c e e0 e1 f AB CE EB AF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.7"
    "And since $AC$ is equal to $CE$, the angle $EAC$ is also equal to the (angle) $AEC$ [Prop.~1.5]."
    (step7 : ∠ e:a:c = ∠ a:e:c) := by euclid_apply (helper_2_9_step7 a b c e e0 e1 AB EA CE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.8"
    "And since the (angle) at $C$ is a right-angle, the (sum of the) remaining angles (of triangle $AEC$), $EAC$ and $AEC$, is thus equal to one right-angle [Prop.~1.32]."
    (step8 : ∠ e:a:c + ∠ a:e:c = ∟) := by euclid_apply (helper_2_9_step8 a b c e e0 e1 AB EA CE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.9"
    "And they are equal."
    (step9 : ∠ e:a:c = ∠ a:e:c) := by euclid_apply (helper_2_9_step9 a c e (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.10"
    "Thus, (angles) $CEA$ and $CAE$ are each half a right-angle."
    (step10 : ∠ c:e:a = ∟ / 2 ∧ ∠ c:a:e = ∟ / 2) := by euclid_apply (helper_2_9_step10 a b c e e1 (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.11"
    "So, for the same (reasons), (angles) $CEB$ and $EBC$ are also each half a right-angle."
    (step11 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2) := by euclid_apply (helper_2_9_step11 a b c e e0 e1 AB CE EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.12"
    "Thus, the whole (angle) $AEB$ is a right-angle."
    (step12 : ∠ a:e:b = ∟) := by euclid_apply (helper_2_9_step12 a b c e e0 e1 AB CE EA EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.13"
    "And since $GEF$ is half a right-angle, and $EGF$ (is) a right-angle---for it is equal to the internal and opposite (angle) $ECB$ [Prop.~1.29]---the remaining (angle) $EFG$ is thus half a right-angle [Prop.~1.32]."
    (step13 : ∠ e:g:f = ∟ ∧ ∠ e:f:g = ∟ / 2) := by euclid_apply (helper_2_9_step13 a b c d e f g e0 e1 AB CE EB DF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.14"
    "Thus, angle $GEF$ [is] equal to $EFG$."
    (step14 : ∠ g:e:f = ∠ e:f:g) := by euclid_apply (helper_2_9_step14 a b c d e f g e0 e1 AB CE EB DF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.15"
    "So the side $EG$ is also equal to the (side) $GF$ [Prop.~1.6]."
    (step15 : |(e─g)| = |(g─f)|) := by euclid_apply (helper_2_9_step15 a b c d e f g e0 e1 AB CE EB DF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.16"
    "Again, since the angle at $B$ is half a right-angle, and (angle) $FDB$ (is) a right-angle---for again it is equal to the internal and opposite (angle) $ECB$ [Prop.~1.29]---the remaining (angle) $BFD$ is half a right-angle [Prop.~1.32]."
    (step16 : ∠ f:d:b = ∟ ∧ ∠ b:f:d = ∟ / 2) := by euclid_apply (helper_2_9_step16 a b c d e f g e0 e1 AB CE EB DF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.17"
    "Thus, the angle at $B$ (is) equal to $DFB$."
    (step17 : ∠ f:b:d = ∠ d:f:b) := by euclid_apply (helper_2_9_step17 a b c d e f g e0 e1 AB CE EB DF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.18"
    "So the side $FD$ is also equal to the side $DB$ [Prop.~1.6]."
    (step18 : |(f─d)| = |(d─b)|) := by euclid_apply (helper_2_9_step18 a b c d e f e0 e1 AB CE EB DF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.19"
    "And since $AC$ is equal to $CE$, the (square) on $AC$ (is) also equal to the (square) on $CE$."
    (step19 : |(a─c)| * |(a─c)| = |(c─e)| * |(c─e)|) := by euclid_apply (helper_2_9_step19 a c e (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.20"
    "Thus, the (sum of the) squares on $AC$ and $CE$ is double the (square) on $AC$."
    (step20 : |(a─c)| * |(a─c)| + |(c─e)| * |(c─e)| = 2 * (|(a─c)| * |(a─c)|)) := by euclid_apply (helper_2_9_step20 a c e (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.21"
    "And the square on $EA$ is equal to the (sum of the) squares on $AC$ and $CE$. For angle $ACE$ (is) a right-angle [Prop.~1.47]."
    (step21 : |(e─a)| * |(e─a)| = |(a─c)| * |(a─c)| + |(c─e)| * |(c─e)|) := by euclid_apply (helper_2_9_step21 a b c e e0 e1 AB CE EA (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.22"
    "Thus, the (square) on $EA$ is double the (square) on $AC$."
    (step23 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) := by euclid_apply (helper_2_9_step23 a c e (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.23"
    "Again, since $EG$ is equal to $GF$, the (square) on $EG$ (is) also equal to the (square) on $GF$."
    (step24 : |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)|) := by euclid_apply (helper_2_9_step24 e f g (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.24"
    "Thus, the (sum of the squares) on $EG$ and $GF$ is double the square on $GF$."
    (step25 : |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)| = 2 * (|(g─f)| * |(g─f)|)) := by euclid_apply (helper_2_9_step25 e f g (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.25"
    "And the square on $EF$ is equal to the (sum of the) squares on $EG$ and $GF$ [Prop.~1.47]."
    (step26 : |(e─f)| * |(e─f)| = |(e─g)| * |(e─g)| + |(g─f)| * |(g─f)|) := by euclid_apply (helper_2_9_step26 a b c d e f g e0 e1 AB CE EB DF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.26"
    "Thus, the square on $EF$ is double the (square) on $GF$."
    (step27 : |(e─f)| * |(e─f)| = 2 * (|(g─f)| * |(g─f)|)) := by euclid_apply (helper_2_9_step27 e f g (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.27"
    "And $GF$ (is) equal to $CD$ [Prop.~1.34]."
    (step28 : |(g─f)| = |(c─d)|) := by euclid_apply (helper_2_9_step28 a b c d e f g e0 e1 AB CE EB DF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.28"
    "Thus, the (square) on $EF$ is double the (square) on $CD$."
    (step29 : |(e─f)| * |(e─f)| = 2 * (|(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_9_step29 c d e f g (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.29"
    "And the (square) on $EA$ is also double the (square) on $AC$."
    (step30 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) := by euclid_apply (helper_2_9_step30 a c e (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.30"
    "Thus, the (sum of the) squares on $AE$ and $EF$ is double the (sum of the) squares on $AC$ and $CD$."
    (step31 : |(e─a)| * |(e─a)| + |(e─f)| * |(e─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_9_step31 a c d e f (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.31"
    "And the square on $AF$ is equal to the (sum of the squares) on $AE$ and $EF$. For the angle $AEF$ is a right-angle [Prop.~1.47]."
    (step32 : |(a─f)| * |(a─f)| = |(e─a)| * |(e─a)| + |(e─f)| * |(e─f)|) := by euclid_apply (helper_2_9_step32 a b c d e f e0 e1 AB CE EA EB DF AF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.32"
    "Thus, the square on $AF$ is double the (sum of the squares) on $AC$ and $CD$."
    (step34 : |(a─f)| * |(a─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_9_step34 a c d e f (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.33"
    "And the (sum of the squares) on $AD$ and $DF$ (is) equal to the (square) on $AF$. For the angle at $D$ is a right-angle [Prop.~1.47]."
    (step35 : |(a─d)| * |(a─d)| + |(d─f)| * |(d─f)| = |(a─f)| * |(a─f)|) := by euclid_apply (helper_2_9_step35 a b c d e f e0 e1 AB CE DF EB AF FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.34"
    "Thus, the (sum of the squares) on $AD$ and $DF$ is double the (sum of the) squares on $AC$ and $CD$."
    (step37 : |(a─d)| * |(a─d)| + |(d─f)| * |(d─f)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_9_step37 a c d f (by assumption) (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.35"
    "And $DF$ (is) equal to $DB$."
    (step38 : |(d─f)| = |(d─b)|) := by euclid_apply (helper_2_9_step38 b d f (by assumption)); (try split_ands) <;> assumption

  euclid_sentence "2.9.36"
    "Thus, the (sum of the) squares on $AD$ and $DB$ is double the (sum of the) squares on $AC$ and $CD$."
    (step39 : |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
      2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_9_step39 a b c d f (by assumption) (by assumption)); (try split_ands) <;> assumption

  exact step39
  euclid_conclude_sentence "2.9.37"
    "Thus, if a straight-line is cut into equal and unequal (pieces, then) the (sum of the) squares on the unequal pieces of the whole (straight-line) is double the (sum of the) square on half (the straight-line) and (the square) on the (difference) between the (equal and unequal) pieces. (Which is) the very thing it was required to show."

end Elements.Book2
