import SystemE
import Book1.Prop03.Main
import Book1Variants.Prop11
import Book1.Prop31.Main
import Mathlib.Tactic.Linarith
import Book2.Prop10.step1
import Book2.Prop10.step2
import Book2.Prop10.step3
import Book2.Prop10.step4
import Book2.Prop10.step5
import Book2.Prop10.step6
import Book2.Prop10.step7
import Book2.Prop10.step8
import Book2.Prop10.step9
import Book2.Prop10.step10
import Book2.Prop10.step11
import Book2.Prop10.step12
import Book2.Prop10.step13
import Book2.Prop10.step14
import Book2.Prop10.step15
import Book2.Prop10.step16
import Book2.Prop10.step17
import Book2.Prop10.step18
import Book2.Prop10.step19
import Book2.Prop10.step20
import Book2.Prop10.step21
import Book2.Prop10.step22
import Book2.Prop10.step23
import Book2.Prop10.step24
import Book2.Prop10.step25
import Book2.Prop10.step26
import Book2.Prop10.step27
import Book2.Prop10.step28
import Book2.Prop10.step29
import Book2.Prop10.step30
import Book2.Prop10.step31
import Book2.Prop10.step32
import Book2.Prop10.step33
import Book2.Prop10.step34
import Book2.Prop10.step35
import Book2.Prop10.step36
import Book2.Prop10.step37
import Book2.Prop10.step38
import Book2.Prop10.step39
import Book2.Prop10.step40
import Book2.Prop10.step41
import Book2.Prop10.step21_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

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
    (step1 : ∠ a:c:e = ∟) := by euclid_apply (helper_2_10_step1 a b c e e0 e1 AC' CE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AC'; assumption)) (by euclid_assumption "" (show c.onLine AC'; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show between c e0 e1; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)))

  euclid_sentence "2.10.2"
    "and let it be made equal to each of $AC$ and $CB$ [Prop.~1.3],"
    (step2 : |(c─e)| = |(a─c)| ∧ |(c─e)| = |(c─b)|) := by euclid_apply (helper_2_10_step2 a b c e (by euclid_assumption "" (show |(c─e)| = |(a─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(c─b)|; assumption)))

  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  euclid_sentence "2.10.3"
    "and let $EA$ and $EB$ be joined."
    (step3 : distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB) := by euclid_apply (helper_2_10_step3 a b c e e0 e1 AD CE EA EB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)))

  euclid_apply (proposition_31 e a d AD) as EF
  euclid_sentence "2.10.4"
    "And let $EF$ be drawn through $E$, parallel to $AD$ [Prop.~1.31],"
    (step4 : e.onLine EF ∧ ¬(EF.intersectsLine AD)) := by euclid_apply (helper_2_10_step4 e EF AD (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)))

  euclid_apply (proposition_31 d c e0 CE) as FD
  euclid_sentence "2.10.5"
    "and let $FD$ be drawn through $D$, parallel to $CE$ [Prop.~1.31]."
    (step5 : d.onLine FD ∧ ¬(FD.intersectsLine CE)) := by euclid_apply (helper_2_10_step5 d FD CE (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)))

  euclid_apply (intersection_lines EF FD) as f
  -- @assumption_valid
  have step6_assumption1 : ¬(FD.intersectsLine CE) := by assumption
  -- @assumption ("the parallel straight-lines $EC$ and $FD$", ¬(FD.intersectsLine CE))
  euclid_sentence "2.10.6"
    "And since some straight-line $EF$ falls across the parallel straight-lines $EC$ and $FD$, the (internal angles) $CEF$ and $EFD$ are thus equal to two right-angles [Prop.~1.29]."
    (step6 : ∠ c:e:f + ∠ e:f:d = ∟ + ∟) := by euclid_apply (helper_2_10_step6 a b c d e e0 e1 f AD CE EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "the parallel straight-lines $EC$ and $FD$" (show ¬(FD.intersectsLine CE); assumption)))

  euclid_sentence "2.10.7"
    "Thus, $FEB$ and $EFD$ are less than two right-angles."
    (step7 : ∠ f:e:b + ∠ e:f:d < ∟ + ∟) := by euclid_apply (helper_2_10_step7 a b c d e e0 e1 f AD CE EF FD EB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ c:e:f + ∠ e:f:d = ∟ + ∟; assumption)))

  euclid_sentence "2.10.8"
    "And (straight-lines) produced from (internal angles whose sum is) less than two right-angles meet together [Post.~5]."
    (step8 : EB.intersectsLine FD) := by euclid_apply (helper_2_10_step8 a b c d e e0 e1 f AD CE EF FD EB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ c:e:f + ∠ e:f:d = ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ f:e:b + ∠ e:f:d < ∟ + ∟; assumption)))

  euclid_sentence "2.10.9"
    "Thus, being produced in the direction of $B$ and $D$, the (straight-lines) $EB$ and $FD$ will meet."
    (step9 : EB.intersectsLine FD) := by euclid_apply (helper_2_10_step9 EB FD (by euclid_assumption "" (show EB.intersectsLine FD; assumption)))

  euclid_apply (intersection_lines EB FD) as g
  euclid_apply (line_from_points a g) as AG
  euclid_sentence "2.10.10"
    "Let them be produced, and let them meet together at $G$, and let $AG$ be joined."
    (step10 : distinctPointsOnLine a g AG) := by euclid_apply (helper_2_10_step10 a b c e e0 e1 g AD CE EB AG (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)))

  -- @assumption_valid
  have step11_assumption1 : |(c─e)| = |(a─c)| := by assumption
  -- @assumption ("$AC$ is equal to $CE$", |(c─e)| = |(a─c)|)
  euclid_sentence "2.10.11"
    "And since $AC$ is equal to $CE$, angle $EAC$ is also equal to (angle) $AEC$ [Prop.~1.5]."
    (step11 : ∠ e:a:c = ∠ a:e:c) := by euclid_apply (helper_2_10_step11 a b c e e0 e1 AD EA CE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "$AC$ is equal to $CE$" (show |(c─e)| = |(a─c)|; assumption)))

  -- @assumption_valid
  have step12_assumption1 : ∠ a:c:e = ∟ := by assumption
  -- @assumption ("the (angle) at $C$ (is) a right-angle", ∠ a:c:e = ∟)
  euclid_sentence "2.10.12"
    "And the (angle) at $C$ (is) a right-angle."
    (step12 : ∠ a:c:e = ∟) := by euclid_apply (helper_2_10_step12 a c e (by euclid_assumption "the (angle) at $C$ (is) a right-angle" (show ∠ a:c:e = ∟; assumption)))

  euclid_sentence "2.10.13"
    "Thus, $EAC$ and $AEC$ [are] each half a right-angle [Prop.~1.32]."
    (step13 : ∠ e:a:c = ∟ / 2 ∧ ∠ a:e:c = ∟ / 2) := by euclid_apply (helper_2_10_step13 a b c e e0 e1 AD EA CE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ e:a:c = ∠ a:e:c; assumption)))

  euclid_sentence "2.10.14"
    "So, for the same (reasons), $CEB$ and $EBC$ are also each half a right-angle."
    (step14 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2) := by euclid_apply (helper_2_10_step14 a b c e e0 e1 AD CE EB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ a:c:e = ∟; assumption)))

  euclid_sentence "2.10.15"
    "Thus, (angle) $AEB$ is a right-angle."
    (step15 : ∠ a:e:b = ∟) := by euclid_apply (helper_2_10_step15 a b c e e0 e1 AD CE EA EB (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ e:a:c = ∟ / 2 ∧ ∠ a:e:c = ∟ / 2; assumption)) (by euclid_assumption "" (show ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2; assumption)))

  -- @assumption_valid
  have step16_assumption1 : ∠ e:b:c = ∟ / 2 := by linarith
  -- @assumption ("since $EBC$ is half a right-angle", ∠ e:b:c = ∟ / 2, use_override step14.2)
  euclid_sentence "2.10.16"
    "And since $EBC$ is half a right-angle, $DBG$ (is) thus also half a right-angle [Prop.~1.15]."
    (step16 : ∠ d:b:g = ∟ / 2) := by euclid_apply (helper_2_10_step16 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "since $EBC$ is half a right-angle" (show ∠ e:b:c = ∟ / 2; exact step14.2)))

  euclid_sentence "2.10.17"
    "And $BDG$ is also a right-angle. For it is equal to $DCE$. For (they are) alternate (angles) [Prop.~1.29]."
    (step17 : ∠ b:d:g = ∟) := by euclid_apply (helper_2_10_step17 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show between c e0 e1; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ a:c:e = ∟; assumption)))

  euclid_sentence "2.10.18"
    "Thus, the remaining (angle) $DGB$ is half a right-angle."
    (step18 : ∠ d:g:b = ∟ / 2) := by euclid_apply (helper_2_10_step18 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ d:b:g = ∟ / 2; assumption)) (by euclid_assumption "" (show ∠ b:d:g = ∟; assumption)))

  euclid_sentence "2.10.19"
    "Thus, $DGB$ is equal to $DBG$."
    (step19 : ∠ d:g:b = ∠ d:b:g) := by euclid_apply (helper_2_10_step19 d b g (by euclid_assumption "" (show ∠ d:b:g = ∟ / 2; assumption)) (by euclid_assumption "" (show ∠ d:g:b = ∟ / 2; assumption)))

  euclid_sentence "2.10.20"
    "So side $BD$ is also equal to side $GD$ [Prop.~1.6]."
    (step20 : |(b─d)| = |(g─d)|) := by euclid_apply (helper_2_10_step20 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ d:g:b = ∠ d:b:g; assumption)))

  -- @assumption_gap
  have step21_assumption1 : ∠ e:g:f = ∟ / 2 := by euclid_apply (helper_2_10_step21_assumption1 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ d:g:b = ∟ / 2; assumption)))
  -- @assumption ("$EGF$ is half a right-angle", ∠ e:g:f = ∟ / 2)
  euclid_sentence "2.10.21"
    "Again, since $EGF$ is half a right-angle, and the (angle) at $F$ (is) a right-angle, for it is equal to the opposite (angle) at $C$ [Prop.~1.34], the remaining (angle) $FEG$ is thus half a right-angle."
    (step21 : ∠ f:e:g = ∟ / 2) := by euclid_apply (helper_2_10_step21 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ a:c:e = ∟; assumption)) (by euclid_assumption "" (show ∠ d:g:b = ∟ / 2; assumption)) (by euclid_assumption "$EGF$ is half a right-angle" (show ∠ e:g:f = ∟ / 2; assumption)))

  euclid_sentence "2.10.22"
    "Thus, angle $EGF$ (is) equal to $FEG$."
    (step22 : ∠ e:g:f = ∠ f:e:g) := by euclid_apply (helper_2_10_step22 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ d:g:b = ∟ / 2; assumption)) (by euclid_assumption "" (show ∠ f:e:g = ∟ / 2; assumption)))

  euclid_sentence "2.10.23"
    "So the side $GF$ is also equal to the side $EF$ [Prop.~1.6]."
    (step23 : |(g─f)| = |(e─f)|) := by euclid_apply (helper_2_10_step23 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ e:g:f = ∠ f:e:g; assumption)))

  -- @assumption_valid
  have step24_assumption1 : |(c─e)| = |(a─c)| := by assumption
  -- @assumption ("$EC$ is equal to $CA$", |(c─e)| = |(a─c)|)
  euclid_sentence "2.10.24"
    "And since [$EC$ is equal to $CA$] the square on $EC$ is [also] equal to the square on $CA$."
    (step24 : |(e─c)| * |(e─c)| = |(c─a)| * |(c─a)|) := by euclid_apply (helper_2_10_step24 a c e (by euclid_assumption "$EC$ is equal to $CA$" (show |(c─e)| = |(a─c)|; assumption)))

  euclid_sentence "2.10.25"
    "Thus, the (sum of the) squares on $EC$ and $CA$ is double the square on $CA$."
    (step25 : |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)| = 2 * (|(c─a)| * |(c─a)|)) := by euclid_apply (helper_2_10_step25 a c e (by euclid_assumption "" (show |(e─c)| * |(e─c)| = |(c─a)| * |(c─a)|; assumption)))

  euclid_sentence "2.10.26"
    "And the (square) on $EA$ is equal to the (sum of the squares) on $EC$ and $CA$ [Prop.~1.47]."
    (step26 : |(e─a)| * |(e─a)| = |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)|) := by euclid_apply (helper_2_10_step26 a b c d e e0 e1 f g AD CE EA EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ a:c:e = ∟; assumption)))

  euclid_sentence "2.10.27"
    "Thus, the square on $EA$ is double the square on $AC$."
    (step27 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) := by euclid_apply (helper_2_10_step27 a c e (by euclid_assumption "" (show |(e─a)| * |(e─a)| = |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)|; assumption)) (by euclid_assumption "" (show |(e─c)| * |(e─c)| + |(c─a)| * |(c─a)| = 2 * (|(c─a)| * |(c─a)|); assumption)))

  -- @assumption_valid
  have step28_assumption1 : |(g─f)| = |(e─f)| := by assumption
  -- @assumption ("$FG$ is equal to $EF$", |(g─f)| = |(e─f)|)
  euclid_sentence "2.10.28"
    "Again, since $FG$ is equal to $EF$, the (square) on $FG$ is also equal to the (square) on $FE$."
    (step28 : |(f─g)| * |(f─g)| = |(f─e)| * |(f─e)|) := by euclid_apply (helper_2_10_step28 e f g (by euclid_assumption "$FG$ is equal to $EF$" (show |(g─f)| = |(e─f)|; assumption)))

  euclid_sentence "2.10.29"
    "Thus, the (sum of the squares) on $GF$ and $FE$ is double the (square) on $EF$."
    (step29 : |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)| = 2 * (|(e─f)| * |(e─f)|)) := by euclid_apply (helper_2_10_step29 e f g (by euclid_assumption "" (show |(f─g)| * |(f─g)| = |(f─e)| * |(f─e)|; assumption)))

  euclid_sentence "2.10.30"
    "And the (square) on $EG$ is equal to the (sum of the squares) on $GF$ and $FE$ [Prop.~1.47]."
    (step30 : |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)|) := by euclid_apply (helper_2_10_step30 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ a:c:e = ∟; assumption)))

  euclid_sentence "2.10.31"
    "Thus, the (square) on $EG$ is double the (square) on $EF$."
    (step31 : |(e─g)| * |(e─g)| = 2 * (|(e─f)| * |(e─f)|)) := by euclid_apply (helper_2_10_step31 e f g (by euclid_assumption "" (show |(e─g)| * |(e─g)| = |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)|; assumption)) (by euclid_assumption "" (show |(g─f)| * |(g─f)| + |(f─e)| * |(f─e)| = 2 * (|(e─f)| * |(e─f)|); assumption)))

  euclid_sentence "2.10.32"
    "And $EF$ (is) equal to $CD$ [Prop.~1.34]."
    (step32 : |(e─f)| = |(c─d)|) := by euclid_apply (helper_2_10_step32 a b c d e e0 e1 f g AD CE EB EF FD (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)))

  euclid_sentence "2.10.33"
    "Thus, the square on $EG$ is double the (square) on $CD$."
    (step33 : |(e─g)| * |(e─g)| = 2 * (|(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_10_step33 c d e f g (by euclid_assumption "" (show |(e─g)| * |(e─g)| = 2 * (|(e─f)| * |(e─f)|); assumption)) (by euclid_assumption "" (show |(e─f)| = |(c─d)|; assumption)))

  euclid_sentence "2.10.34"
    "But it was also shown that the (square) on $EA$ (is) double the (square) on $AC$."
    (step34 : |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|)) := by euclid_apply (helper_2_10_step34 a c e (by euclid_assumption "" (show |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|); assumption)))

  euclid_sentence "2.10.35"
    "Thus, the (sum of the) squares on $AE$ and $EG$ is double the (sum of the) squares on $AC$ and $CD$."
    (step35 : |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_10_step35 a c d e g (by euclid_assumption "" (show |(e─a)| * |(e─a)| = 2 * (|(a─c)| * |(a─c)|); assumption)) (by euclid_assumption "" (show |(e─g)| * |(e─g)| = 2 * (|(c─d)| * |(c─d)|); assumption)))

  euclid_sentence "2.10.36"
    "And the square on $AG$ is equal to the (sum of the) squares on $AE$ and $EG$ [Prop.~1.47]."
    (step36 : |(a─g)| * |(a─g)| = |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)|) := by euclid_apply (helper_2_10_step36 a b c d e e0 e1 f g AD CE EA EB EF FD AG (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show ∠ a:e:b = ∟; assumption)))

  euclid_sentence "2.10.37"
    "Thus, the (square) on $AG$ is double the (sum of the squares) on $AC$ and $CD$."
    (step37 : |(a─g)| * |(a─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_10_step37 a c d e g (by euclid_assumption "" (show |(a─g)| * |(a─g)| = |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)|; assumption)) (by euclid_assumption "" (show |(a─e)| * |(a─e)| + |(e─g)| * |(e─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|); assumption)))

  euclid_sentence "2.10.38"
    "And the (sum of the squares) on $AD$ and $DG$ is equal to the (square) on $AG$ [Prop.~1.47]."
    (step38 : |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = |(a─g)| * |(a─g)|) := by euclid_apply (helper_2_10_step38 a b c d e e0 e1 f g AD CE EB EF FD AG (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AD; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ∠ a:c:e0 = ∟; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine FD; assumption)) (by euclid_assumption "" (show d.onLine FD; assumption)) (by euclid_assumption "" (show f.onLine FD; assumption)) (by euclid_assumption "" (show g.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show ¬EF.intersectsLine AD; assumption)) (by euclid_assumption "" (show ¬FD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ∠ b:d:g = ∟; assumption)))

  euclid_sentence "2.10.39"
    "Thus, the (sum of the) [squares] on $AD$ and $DG$ is double the (sum of the) [squares] on $AC$ and $CD$."
    (step39 : |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_10_step39 a c d g (by euclid_assumption "" (show |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = |(a─g)| * |(a─g)|; assumption)) (by euclid_assumption "" (show |(a─g)| * |(a─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|); assumption)))

  euclid_sentence "2.10.40"
    "And $DG$ (is) equal to $DB$."
    (step40 : |(d─g)| = |(d─b)|) := by euclid_apply (helper_2_10_step40 b d g (by euclid_assumption "" (show |(b─d)| = |(g─d)|; assumption)))

  euclid_sentence "2.10.41"
    "Thus, the (sum of the) [squares] on $AD$ and $DB$ is double the (sum of the) squares on $AC$ and $CD$."
    (step41 : |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
      2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|)) := by euclid_apply (helper_2_10_step41 a b c d g (by euclid_assumption "" (show |(a─d)| * |(a─d)| + |(d─g)| * |(d─g)| = 2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|); assumption)) (by euclid_assumption "" (show |(d─g)| = |(d─b)|; assumption)))

  exact step41
  euclid_conclude_sentence "2.10.42"
    "Thus, if a straight-line is cut in half, and any straight-line added to it straight-on, (then) the sum of the square on the whole (straight-line) with the (straight-line) having been added, and the (square) on the (straight-line) having been added, is double the (sum of the square) on half (the straight-line), and the square described on the sum of half (the straight-line) and (straight-line) having been added, as on one (complete straight-line). (Which is) the very thing it was required to show."

end Elements.Book2
