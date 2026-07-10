import SystemE
import Book1Variants.Prop46
import Book1.Prop31.Main
import Book2.Prop03.step1
import Book2.Prop03.step2
import Book2.Prop03.step3
import Book2.Prop03.step4
import Book2.Prop03.step5
import Book2.Prop03.step6
import Book2.Prop03.step7
import Book2.Prop03.step8
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2
theorem proposition_3 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| :=
by
  euclid_intros
  euclid_intro_sentence "2.3.0"
    "If a straight-line is cut at random, (then) the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the rectangle contained by (both of) the pieces, and the square on the aforementioned piece. For let the straight-line $AB$ be cut, at random, at (point) $C$. I say that the rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by $AC$ and $CB$, plus the square on $BC$."

  euclid_apply (Elements.Book1.proposition_46 c b AB) as (d, e, DE, CD, BE)
  euclid_apply (Elements.Book1.proposition_31 a c d CD) as AF
  euclid_apply (intersection_lines AF DE) as f
  euclid_sentence "2.3.1"
    "For let the square $CDEB$ be described on $CB$ [Prop.~1.46],"
    (step1 : |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧ |(d─e)| = |(c─b)| ∧
      (∠ b:c:d = ∟) ∧ (∠ c:d:e = ∟) ∧ (∠ c:b:e = ∟) ∧ (∠ b:e:d = ∟)) := by euclid_apply (helper_2_3_step1 b c d e (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:e:d = ∟; assumption)))
  --He talks of F even though F is not constructed yet. This is why we must relax the faithfulness criterion or it would not compile.
  euclid_sentence "2.3.2"
    "and let $ED$ be drawn through to $F$,"
    (step2 : f.onLine DE ∧ between e d f) := by euclid_apply (helper_2_3_step2 a b c d e f AB DE CD BE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)))
  -- sepcifically ideally prop 31 is used in this block. This introduces the line AF. However, the point F needs this line AF to be defined, and euclid kinda messes up the order so we sacrifice faithfulness slightly for correctness.
  euclid_sentence "2.3.3"
    "and let $AF$ be drawn through $A$, parallel to either of $CD$ or $BE$ [Prop.~1.31]."
    (step3 : a.onLine AF ∧ ¬(AF.intersectsLine CD)) := by euclid_apply (helper_2_3_step3 a AF CD (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)))

  euclid_sentence "2.3.4"
    "So the (rectangle) $AE$ is equal to the (rectangle) $AD$ and the (square) $CE$."
    (step4 : Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b)) := by euclid_apply (helper_2_3_step4 a b c d e f AB DE CD BE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))

  -- @assumption ("$BE$ (is) equal to $BC$", |(b─e)| = |(c─b)|)
  euclid_sentence "2.3.5"
    "And $AE$ is the rectangle contained by $AB$ and $BC$. For it is contained by $AB$ and $BE$, and $BE$ (is) equal to $BC$."
    (step5 : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)|) := by euclid_apply (helper_2_3_step5 a b c d e f AB DE CD BE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "$BE$ (is) equal to $BC$" (show |(b─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:e:d = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))

  -- @assumption ("$DC$ (is) equal to $CB$", |(c─d)| = |(c─b)|)
  euclid_sentence "2.3.6"
    "And $AD$ (is) the (rectangle contained) by $AC$ and $CB$. For $DC$ (is) equal to $CB$."
    (step6 : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)|) := by euclid_apply (helper_2_3_step6 a b c d e f AB DE CD BE AF (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "$DC$ (is) equal to $CB$" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:e:d = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(AF.intersectsLine CD); assumption)))

  euclid_sentence "2.3.7"
    "And $DB$ (is) the square on $CB$."
    (step7 : Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)|) := by euclid_apply (helper_2_3_step7 a b c d e AB DE CD BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show ∠ c:b:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:e:d = ∟; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CD.intersectsLine BE); assumption)))

  euclid_sentence "2.3.8"
    "Thus, the rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by $AC$ and $CB$, plus the square on $BC$."
    (step8 : |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)|) := by euclid_apply (helper_2_3_step8 a b c d e f (by euclid_assumption "" (show Triangle.area △ a:f:e + Triangle.area △ a:e:b = (Triangle.area △ a:f:d + Triangle.area △ a:d:c) + (Triangle.area △ c:d:e + Triangle.area △ c:e:b); assumption)) (by euclid_assumption "" (show Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)|; assumption)) (by euclid_assumption "" (show Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)|; assumption)) (by euclid_assumption "" (show Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)|; assumption)))

  exact step8
  euclid_conclude_sentence "2.3.9"
    "Thus, if a straight-line is cut at random, (then) the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the rectangle contained by (both of) the pieces, and the square on the aforementioned piece. (Which is) the very thing it was required to show."

end Elements.Book2
