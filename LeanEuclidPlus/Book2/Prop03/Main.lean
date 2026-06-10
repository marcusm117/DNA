import SystemE
import Book.Prop46
import Book.Prop31

namespace Elements.Book2

/-
═══════════════════════════════════════════════════════════════════════════════
STATEMENT — Prop 2.3
Convention: "rectangle contained by X and Y" = length-product |X|·|Y|
            "square on X"                     = |X|·|X|
            (LeanEuclid, cf. Book 1 Prop 47/48; matches Book2/Prop01).
───────────────────────────────────────────────────────────────────────────────
If a straight-line is cut at random, (then) the rectangle contained by the whole
(straight-line), and one of the pieces (of the straight-line), is equal to the
rectangle contained by (both of) the pieces, and the square on the aforementioned
piece.

  premises : line AB (endpoints a b); point c cutting AB at random  (between a c b)
  GOAL     : rect(AB,BC) = rect(AC,CB) + square(BC)
             |a─b|·|b─c| = |a─c|·|c─b| + |b─c|·|b─c|
═══════════════════════════════════════════════════════════════════════════════
-/

-- For let the straight-line $AB$ be cut, at random, at (point) $C$. I say that the
-- rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by
-- $AC$ and $CB$, plus the square on $BC$.
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
    "For let the square $CDEB$ be described on $CB$ [Prop.~1.46], and let $ED$ be drawn through to $F$, and let $AF$ be drawn through $A$, parallel to either of $CD$ or $BE$ [Prop.~1.31]."
    (step1 : formParallelogram d e c b DE AB CD BE ∧ |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧
      |(d─e)| = |(c─b)| ∧ (∠ b:c:d = ∟) ∧ a.onLine AF ∧ f.onLine AF ∧ f.onLine DE) := by sorry

  euclid_sentence "2.3.2"
    "So the (rectangle) $AE$ is equal to the (rectangle) $AD$ and the (square) $CE$."
    (step2 : Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b)) := by sorry

  euclid_sentence "2.3.3"
    "And $AE$ is the rectangle contained by $AB$ and $BC$. For it is contained by $AB$ and $BE$, and $BE$ (is) equal to $BC$."
    (step3 : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)|) := by sorry

  euclid_sentence "2.3.4"
    "And $AD$ (is) the (rectangle contained) by $AC$ and $CB$. For $DC$ (is) equal to $CB$."
    (step4 : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)|) := by sorry

  euclid_sentence "2.3.5"
    "And $DB$ (is) the square on $CB$."
    (step5 : Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)|) := by sorry

  euclid_sentence "2.3.6"
    "Thus, the rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by $AC$ and $CB$, plus the square on $BC$."
    (step6 : |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)|) := by sorry

  exact step6
  euclid_conclude_sentence "2.3.7"
    "Thus, if a straight-line is cut at random, (then) the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the rectangle contained by (both of) the pieces, and the square on the aforementioned piece. (Which is) the very thing it was required to show."

end Elements.Book2