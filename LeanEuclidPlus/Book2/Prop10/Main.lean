import SystemE
import Book.Prop03
import Book.Prop11
import Book.Prop31
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_10 : ∀ (a b c d : Point) (AD : Line),
  distinctPointsOnLine a d AD ∧ c.onLine AD ∧ b.onLine AD ∧
  between a c b ∧ between a b d ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
    2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) := by
  euclid_intros
  euclid_intro_sentence "2.10.0"
    "If a straight-line is cut in half, and any straight-line added to it straight-on, (then) the sum of the square on the whole (straight-line) with the (straight-line) having been added, and the (square) on the (straight-line) having been added, is double the (sum of the square) on half (the straight-line), and the square described on the sum of half (the straight-line) and (straight-line) having been added, as on one (complete straight-line). For let any straight-line $AB$ be cut in half at (point) $C$, and let any straight-line $BD$ be added to it straight-on. I say that the (sum of the) squares on $AD$ and $DB$ is double the (sum of the) squares on $AC$ and $CD$."

  euclid_apply (proposition_11 a b c AD) as e0
  euclid_apply (line_from_points c e0) as CE
  euclid_apply (line_from_points a c) as AC'
  euclid_apply (extend_point_longer CE c e0 (a─c)) as e1
  euclid_apply (proposition_3 c e1 a c CE AC') as e
  euclid_sentence "2.10.1"
    "For let $CE$ be drawn from point $C$, at right-angles to $AB$ [Prop.~1.11],"
    (step1 : ∠ a:c:e = ∟) := by sorry

  euclid_sentence "2.10.2"
    "and let it be made equal to each of $AC$ and $CB$ [Prop.~1.3],"
    (step2 : |(c─e)| = |(a─c)| ∧ |(c─e)| = |(c─b)|) := by sorry

  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_sentence "2.10.3"
    "and let $EA$ and $EB$ be joined."
    (step3 : distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB) := by sorry

  euclid_apply (proposition_31 e a d AD) as EF
  euclid_sentence "2.10.4"
    "And let $EF$ be drawn through $E$, parallel to $AD$ [Prop.~1.31],"
    (step4 : e.onLine EF ∧ ¬(EF.intersectsLine AD)) := by sorry

  euclid_apply (proposition_31 d c e0 CE) as FD
  euclid_sentence "2.10.5"
    "and let $FD$ be drawn through $D$, parallel to $CE$ [Prop.~1.31]."
    (step5 : d.onLine FD ∧ ¬(FD.intersectsLine CE)) := by sorry

  euclid_apply (intersection_lines EF FD) as f
  euclid_sentence "2.10.6"
    "And since some straight-line $EF$ falls across the parallel straight-lines $EC$ and $FD$, the (internal angles) $CEF$ and $EFD$ are thus equal to two right-angles [Prop.~1.29]."
    (step6 : ∠ c:e:f + ∠ e:f:d = ∟ + ∟) := by sorry

  euclid_sentence "2.10.7"
    "Thus, $FEB$ and $EFD$ are less than two right-angles."
    (step7 : ∠ f:e:b + ∠ e:f:d < ∟ + ∟) := by sorry

  euclid_sentence "2.10.8"
    "And (straight-lines) produced from (internal angles whose sum is) less than two right-angles meet together [Post.~5]."
    (step8 : EB.intersectsLine FD) := by sorry

  euclid_sentence "2.10.9"
    "Thus, being produced in the direction of $B$ and $D$, the (straight-lines) $EB$ and $FD$ will meet."
    (step9 : EB.intersectsLine FD) := by sorry

  euclid_apply (intersection_lines EB FD) as g
  euclid_apply (line_from_points a g) as AG
  euclid_sentence "2.10.10"
    "Let them be produced, and let them meet together at $G$, and let $AG$ be joined."
    (step10 : distinctPointsOnLine a g AG) := by sorry

  -- @assumption ("$AC$ is equal to $CE$", |(c─e)| = |(a─c)|)
  euclid_sentence "2.10.11"
    "And since $AC$ is equal to $CE$, angle $EAC$ is also equal to (angle) $AEC$ [Prop.~1.5]."
    (step11 : ∠ e:a:c = ∠ a:e:c) := by sorry

  euclid_sentence "2.10.12"
    "And the (angle) at $C$ (is) a right-angle."
    (step12 : ∠ a:c:e = ∟) := by sorry

  euclid_sentence "2.10.13"
    "Thus, $EAC$ and $AEC$ [are] each half a right-angle [Prop.~1.32]."
    (step13 : ∠ e:a:c = ∟ / 2 ∧ ∠ a:e:c = ∟ / 2) := by sorry

  euclid_sentence "2.10.14"
    "So, for the same (reasons), $CEB$ and $EBC$ are also each half a right-angle."
    (step14 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2) := by sorry

  euclid_sentence "2.10.15"
    "Thus, (angle) $AEB$ is a right-angle."
    (step15 : ∠ a:e:b = ∟) := by sorry

  -- @assumption ("since $EBC$ is half a right-angle", ∠ e:b:c = ∟ / 2, use_override step14.2)
  euclid_sentence "2.10.16"
    "And since $EBC$ is half a right-angle, $DBG$ (is) thus also half a right-angle [Prop.~1.15]."
    (step16 : ∠ d:b:g = ∟ / 2) := by sorry

  euclid_sentence "2.10.17"
    "And $BDG$ is also a right-angle. For it is equal to $DCE$. For (they are) alternate (angles) [Prop.~1.29]."
    (step17 : ∠ b:d:g = ∟) := by sorry

  euclid_sentence "2.10.18"
    "Thus, the remaining (angle) $DGB$ is half a right-angle."
    (step18 : ∠ d:g:b = ∟ / 2) := by sorry

  euclid_sentence "2.10.19"
    "Thus, $DGB$ is equal to $DBG$."
    (step19 : ∠ d:g:b = ∠ d:b:g) := by sorry

  euclid_sentence "2.10.20"
    "So side $BD$ is also equal to side $GD$ [Prop.~1.6]."
    (step20 : |(b─d)| = |(g─d)|) := by sorry

  -- ∠EGF = ∟/2 is derived inside this cone (step21_egf = ∠d:g:b via ray coincidence), not an input.
  euclid_sentence "2.10.21"
    "Again, since $EGF$ is half a right-angle, and the (angle) at $F$ (is) a right-angle, for it is equal to the opposite (angle) at $C$ [Prop.~1.34], the remaining (angle) $FEG$ is thus half a right-angle."
    (step21 : ∠ f:e:g = ∟ / 2) := by sorry

  euclid_sentence "2.10.22"
    "Thus, angle $EGF$ (is) equal to $FEG$."
    (step22 : ∠ e:g:f = ∠ f:e:g) := by sorry

  euclid_sentence "2.10.23"
    "So the side $GF$ is also equal to the side $EF$ [Prop.~1.6]."
    (step23 : |(g─f)| = |(e─f)|) := by sorry

  -- @assumption ("$EC$ is equal to $CA$", |(c─e)| = |(a─c)|)
  euclid_sentence "2.10.24"
    "And since [$EC$ is equal to $CA$] the square on $EC$ is [also] equal to the square on $CA$."
    (step24 : |(e─c)| * |(e─c)| = |(c─a)| * |(c─a)|) := by sorry

  euclid_sentence "2.10.25"
    "Thus, the (sum of the) squares on $EC$ and $CA$ is double the square on $CA$."
    (step25 : |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)| = 2 * (|(c─a)| * |(c─a)|)) := by sorry

  euclid_sentence "2.10.26"
    "And the (square) on $EA$ is equal to the (sum of the squares) on $EC$ and $CA$ [Prop.~1.47]."
    (step26 : |(e─a)| * |(e─a)| = |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)|) := by sorry

  euclid_sentence "2.10.27"
    "Thus, the square on $EA$ is double the square on $AC$."
    (step27 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) := by sorry

  -- @assumption ("$FG$ is equal to $EF$", |(g─f)| = |(e─f)|)
  euclid_sentence "2.10.28"
    "Again, since $FG$ is equal to $EF$, the (square) on $FG$ is also equal to the (square) on $FE$."
    (step28 : |(f─g)| * |(f─g)| = |(f─e)| * |(f─e)|) := by sorry

  euclid_sentence "2.10.29"
    "Thus, the (sum of the squares) on $GF$ and $FE$ is double the (square) on $EF$."
    (step29 : |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)| = 2 * (|(e─f)| * |(e─f)|)) := by sorry

  euclid_sentence "2.10.30"
    "And the (square) on $EG$ is equal to the (sum of the squares) on $GF$ and $FE$ [Prop.~1.47]."
    (step30 : |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)|) := by sorry

  euclid_sentence "2.10.31"
    "Thus, the (square) on $EG$ is double the (square) on $EF$."
    (step31 : |(e─g)| * |(e─g)| = 2 * (|(e─f)| * |(e─f)|)) := by sorry

  euclid_sentence "2.10.32"
    "And $EF$ (is) equal to $CD$ [Prop.~1.34]."
    (step32 : |(e─f)| = |(c─d)|) := by sorry

  euclid_sentence "2.10.33"
    "Thus, the square on $EG$ is double the (square) on $CD$."
    (step33 : |(e─g)| * |(e─g)| = 2 * (|(c─d)| * |(c─d)|)) := by sorry

  euclid_sentence "2.10.34"
    "But it was also shown that the (square) on $EA$ (is) double the (square) on $AC$."
    (step34 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) := by sorry

  euclid_sentence "2.10.35"
    "Thus, the (sum of the) squares on $AE$ and $EG$ is double the (sum of the) squares on $AC$ and $CD$."
    (step35 : |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by sorry

  euclid_sentence "2.10.36"
    "And the square on $AG$ is equal to the (sum of the) squares on $AE$ and $EG$ [Prop.~1.47]."
    (step36 : |(a─g)| * |(a─g)| = |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)|) := by sorry

  euclid_sentence "2.10.37"
    "Thus, the (square) on $AG$ is double the (sum of the squares) on $AC$ and $CD$."
    (step37 : |(a─g)| * |(a─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by sorry

  euclid_sentence "2.10.38"
    "And the (sum of the squares) on $AD$ and $DG$ is equal to the (square) on $AG$ [Prop.~1.47]."
    (step38 : |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = |(a─g)| * |(a─g)|) := by sorry

  euclid_sentence "2.10.39"
    "Thus, the (sum of the) [squares] on $AD$ and $DG$ is double the (sum of the) [squares] on $AC$ and $CD$."
    (step39 : |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by sorry

  euclid_sentence "2.10.40"
    "And $DG$ (is) equal to $DB$."
    (step40 : |(d─g)| = |(d─b)|) := by sorry

  euclid_sentence "2.10.41"
    "Thus, the (sum of the) [squares] on $AD$ and $DB$ is double the (sum of the) squares on $AC$ and $CD$."
    (step41 : |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
      2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by sorry

  exact step41
  euclid_conclude_sentence "2.10.42"
    "Thus, if a straight-line is cut in half, and any straight-line added to it straight-on, (then) the sum of the square on the whole (straight-line) with the (straight-line) having been added, and the (square) on the (straight-line) having been added, is double the (sum of the square) on half (the straight-line), and the square described on the sum of half (the straight-line) and (straight-line) having been added, as on one (complete straight-line). (Which is) the very thing it was required to show."

end Elements.Book2
