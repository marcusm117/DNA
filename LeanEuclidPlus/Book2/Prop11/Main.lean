import SystemE
import Book.Prop46
import Book.Prop10
import Book.Prop03
import Book2.Prop11.step1
import Book2.Prop11.step2
import Book2.Prop11.step3
import Book2.Prop11.step4
import Book2.Prop11.step5
import Book2.Prop11.step6
import Book2.Prop11.step7
import Book2.Prop11.step8
import Book2.Prop11.step9
import Book2.Prop11.step10
import Book2.Prop11.step11
import Book2.Prop11.step12
import Book2.Prop11.step13
import Book2.Prop11.step14
import Book2.Prop11.step15
import Book2.Prop11.step16
import Book2.Prop11.step17
import Book2.Prop11.step18
import Book2.Prop11.step19
import Book2.Prop11.step20
import Book2.Prop11.step21
import Book2.Prop11.step22
import Book2.Prop11.step23
import Book2.Prop11.between_ahb
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

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
    (step1 : formParallelogram c d a b CD AB AC BD ∧ |(c─d)| = |(a─b)| ∧ |(a─c)| = |(a─b)| ∧ |(b─d)| = |(a─b)| ∧ ∠ b:a:c = ∟ ∧ ∠ a:c:d = ∟ ∧ ∠ a:b:d = ∟ ∧ ∠ c:d:b = ∟) := by euclid_apply (helper_2_11_step1 a b c d AB CD AC BD (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide a BD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AC.intersectsLine BD; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(b─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d = ∟; assumption)) (by euclid_assumption "" (show ∠ b:d:c = ∟; assumption)))

  euclid_apply (proposition_10 a c AC) as e
  euclid_sentence "2.11.2"
    "and let $AC$ be cut in half at point $E$ [Prop.~1.10],"
    (step2 : between a e c ∧ |(a─e)| = |(e─c)|) := by euclid_apply (helper_2_11_step2 a e c (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)))

  euclid_apply (line_from_points b e) as BE
  euclid_sentence "2.11.3"
    "and let $BE$ be joined."
    (step3 : distinctPointsOnLine b e BE) := by euclid_apply (helper_2_11_step3 a b c e AB AC BE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)))

  euclid_apply (extend_point_longer AC c a (b─e)) as f0
  euclid_sentence "2.11.4"
    "And let $CA$ be drawn through to (point) $F$,"
    (step4 : between c a f0 ∧ f0.onLine AC) := by euclid_apply (helper_2_11_step4 a c f0 AC (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show f0.onLine AC; assumption)))

  euclid_apply (proposition_3 e f0 b e AC BE) as f
  euclid_sentence "2.11.5"
    "and let $EF$ be made equal to $BE$ [Prop.~1.3]."
    (step5 : between e f f0 ∧ |(e─f)| = |(b─e)|) := by euclid_apply (helper_2_11_step5 e f f0 b (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)))

  euclid_apply (exists_point_opposite AC b) as x
  euclid_apply (proposition_46' a f x AC) as (h, g, GH, AH, FG)
  euclid_sentence "2.11.6"
    "And let the square $FH$ be described on $AF$ [Prop.~1.46],"
    (step6 : formParallelogram h g a f GH AC AH FG ∧ |(h─g)| = |(a─f)| ∧ |(a─h)| = |(a─f)| ∧ |(f─g)| = |(a─f)| ∧ ∠ f:a:h = ∟ ∧ ∠ a:f:g = ∟ ∧ ∠ a:h:g = ∟ ∧ ∠ f:g:h = ∟) := by euclid_apply (helper_2_11_step6 a f h g AC GH AH FG (by euclid_assumption "" (show g ≠ f; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show h.sameSide a FG; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine FG; assumption)) (by euclid_assumption "" (show |(h─g)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(f─g)| = |(a─f)|; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show ∠ a:h:g = ∟; assumption)) (by euclid_assumption "" (show ∠ a:f:g = ∟; assumption)) (by euclid_assumption "" (show ∠ f:g:h = ∟; assumption)))

  euclid_apply (intersection_lines GH CD) as k
  euclid_sentence "2.11.7"
    "and let $GH$ be drawn through to (point) $K$."
    (step7 : k.onLine GH ∧ k.onLine CD) := by euclid_apply (helper_2_11_step7 k GH CD (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)))

  euclid_sentence "2.11.8"
    "I say that $AB$ has been cut at $H$ such as to make the rectangle contained by $AB$ and $BH$ equal to the square on $AH$."
    (step8 : |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)|) := by euclid_apply (helper_2_11_step8 a b c e f f0 g h x AB AC AH GH CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show ¬ x.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show ¬ h.onLine AC; assumption)) (by euclid_assumption "" (show ¬ x.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬ h.sameSide x AC; assumption)))

  -- @assumption ("the straight-line $AC$ has been cut in half at $E$, and $FA$ has been added to it", |(a─e)| = |(e─c)|)
  euclid_sentence "2.11.9"
    "For since the straight-line $AC$ has been cut in half at $E$, and $FA$ has been added to it, the rectangle contained by $CF$ and $FA$, plus the square on $AE$, is thus equal to the square on $EF$ [Prop.~2.6]."
    (step9 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─f)| * |(e─f)|) := by euclid_apply (helper_2_11_step9 a b c e f f0 AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "the straight-line $AC$ has been cut in half at $E$, and $FA$ has been added to it" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)))

  euclid_sentence "2.11.10"
    "And $EF$ (is) equal to $EB$."
    (step10 : |(e─f)| = |(e─b)|) := by euclid_apply (helper_2_11_step10 b e f (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)))

  euclid_sentence "2.11.11"
    "Thus, the (rectangle contained) by $CF$ and $FA$, plus the (square) on $AE$, is equal to the (square) on $EB$."
    (step11 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)|) := by euclid_apply (helper_2_11_step11 a c e f b (by euclid_assumption "" (show |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─f)| * |(e─f)|; assumption)) (by euclid_assumption "" (show |(e─f)| = |(e─b)|; assumption)))

  -- @assumption ("the angle at $A$ (is) a right-angle", ∠ b:a:c = ∟)
  euclid_sentence "2.11.12"
    "But, the (sum of the squares) on $BA$ and $AE$ is equal to the (square) on $EB$. For the angle at $A$ (is) a right-angle [Prop.~1.47]."
    (step12 : |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)|) := by euclid_apply (helper_2_11_step12 a b c e AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "the angle at $A$ (is) a right-angle" (show ∠ b:a:c = ∟; assumption)))

  euclid_sentence "2.11.13"
    "Thus, the (rectangle contained) by $CF$ and $FA$, plus the (square) on $AE$, is equal to the (sum of the squares) on $BA$ and $AE$."
    (step13 : |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)|) := by euclid_apply (helper_2_11_step13 a b c e f (by euclid_assumption "" (show |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)|; assumption)) (by euclid_assumption "" (show |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)| = |(e─b)| * |(e─b)|; assumption)))

  euclid_sentence "2.11.14"
    "Let the square on $AE$ have been subtracted from both."
    (step14 : |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|) := by euclid_apply (helper_2_11_step14 a b c e f (by euclid_assumption "" (show |(c─f)| * |(f─a)| + |(a─e)| * |(a─e)| = |(b─a)| * |(b─a)| + |(a─e)| * |(a─e)|; assumption)))

  euclid_sentence "2.11.15"
    "Thus, the remaining rectangle contained by $CF$ and $FA$ is equal to the square on $AB$."
    (step15 : |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|) := by euclid_apply (helper_2_11_step15 a b c f (by euclid_assumption "" (show |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|; assumption)))

  -- @assumption ("$AF$ (is) equal to $FG$", |(f─g)| = |(a─f)|)
  euclid_sentence "2.11.16"
    "And $FK$ is the (rectangle contained) by $CF$ and $FA$. For $AF$ (is) equal to $FG$."
    (step16 : Triangle.area △ f:g:k + Triangle.area △ f:c:k = |(c─f)| * |(f─a)|) := by euclid_apply (helper_2_11_step16 a b c d e f f0 g h x k AB CD AC BD GH AH FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show ∠ f:g:h = ∟; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine FG; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬x.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.sameSide x AC; assumption)) (by euclid_assumption "" (show ¬x.sameSide b AC; assumption)) (by euclid_assumption "$AF$ (is) equal to $FG$" (show |(f─g)| = |(a─f)|; assumption)))

  euclid_sentence "2.11.17"
    "And $AD$ (is) the (square) on $AB$."
    (step17 : Triangle.area △ a:b:d + Triangle.area △ a:c:d = |(a─b)| * |(a─b)|) := by euclid_apply (helper_2_11_step17 a b c d AB CD AC BD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide a BD; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AC.intersectsLine BD; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)))

  euclid_sentence "2.11.18"
    "Thus, the (rectangle) $FK$ is equal to the (square) $AD$."
    (step18 : Triangle.area △ f:g:k + Triangle.area △ f:c:k = Triangle.area △ a:b:d + Triangle.area △ a:c:d) := by euclid_apply (helper_2_11_step18 a b c d f g k (by euclid_assumption "" (show Triangle.area △ f:g:k + Triangle.area △ f:c:k = |(c─f)| * |(f─a)|; assumption)) (by euclid_assumption "" (show |(c─f)| * |(f─a)| = |(a─b)| * |(a─b)|; assumption)) (by euclid_assumption "" (show Triangle.area △ a:b:d + Triangle.area △ a:c:d = |(a─b)| * |(a─b)|; assumption)))

  euclid_sentence "2.11.19"
    "Let (rectangle) $AK$ be subtracted from both."
    (step19 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d) := by euclid_apply (helper_2_11_step19 a b c d e f f0 g h x k AB CD AC BD GH AH FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show c.sameSide a BD; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine FG; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬AC.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬x.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.sameSide x AC; assumption)) (by euclid_assumption "" (show ¬x.sameSide b AC; assumption)) (by euclid_assumption "" (show Triangle.area △ f:g:k + Triangle.area △ f:c:k = Triangle.area △ a:b:d + Triangle.area △ a:c:d; assumption)))

  euclid_sentence "2.11.20"
    "Thus, the remaining (square) $FH$ is equal to the (rectangle) $HD$."
    (step20 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d) := by euclid_apply (helper_2_11_step20 a f g h b d k (by euclid_assumption "" (show Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d; assumption)))

  -- @assumption ("$AB$ (is) equal to $BD$", |(b─d)| = |(a─b)|)
  euclid_sentence "2.11.21"
    "And $HD$ is the (rectangle contained) by $AB$ and $BH$. For $AB$ (is) equal to $BD$."
    (step21 : Triangle.area △ h:b:d + Triangle.area △ h:k:d = |(a─b)| * |(b─h)|) := by euclid_apply (helper_2_11_step21 a b c d e f f0 g h x k AB CD AC BD GH AH FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show ∠ a:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine FG; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AC.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬x.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.sameSide x AC; assumption)) (by euclid_assumption "" (show ¬x.sameSide b AC; assumption)) (by euclid_assumption "$AB$ (is) equal to $BD$" (show |(b─d)| = |(a─b)|; assumption)))

  euclid_sentence "2.11.22"
    "And $FH$ (is) the (square) on $AH$."
    (step22 : Triangle.area △ f:g:h + Triangle.area △ f:a:h = |(a─h)| * |(a─h)|) := by euclid_apply (helper_2_11_step22 a b c e f f0 g h AB AC GH FG AH (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(f─g)| = |(a─f)|; assumption)) (by euclid_assumption "" (show ∠ f:g:h = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine FG; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)))

  euclid_sentence "2.11.23"
    "Thus, the rectangle contained by $AB$ and $BH$ is equal to the square on $HA$."
    (step23 : |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)|) := by euclid_apply (helper_2_11_step23 a b d f g h k (by euclid_assumption "" (show Triangle.area △ f:g:h + Triangle.area △ f:a:h = Triangle.area △ h:b:d + Triangle.area △ h:k:d; assumption)) (by euclid_assumption "" (show Triangle.area △ h:b:d + Triangle.area △ h:k:d = |(a─b)| * |(b─h)|; assumption)) (by euclid_assumption "" (show Triangle.area △ f:g:h + Triangle.area △ f:a:h = |(a─h)| * |(a─h)|; assumption)))

  use h
  have between_ahb : between a h b := by euclid_apply (helper_2_11_between_ahb a b c e f f0 h g x AB AC AH GH CD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine AC; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ f:a:h = ∟; assumption)) (by euclid_assumption "" (show between a e c; assumption)) (by euclid_assumption "" (show |(a─e)| = |(e─c)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show between c a f0; assumption)) (by euclid_assumption "" (show between e f f0; assumption)) (by euclid_assumption "" (show |(e─f)| = |(b─e)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─f)|; assumption)) (by euclid_assumption "" (show ¬ x.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show ¬ h.onLine AC; assumption)) (by euclid_assumption "" (show ¬ x.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬ h.sameSide x AC; assumption)))
  refine ⟨between_ahb, step23⟩
  euclid_conclude_sentence "2.11.24"
    "Thus, the given straight-line $AB$ has been cut at (point) $H$ such as to make the rectangle contained by $AB$ and $BH$ equal to the square on $HA$. (Which is) the very thing it was required to do."

end Elements.Book2
