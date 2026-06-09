import SystemE
import Book.Prop11
import Book.Prop42
import Book.Prop45
import Book2.Helper14_product

namespace Elements.Book2

open Elements.Book1

/-
Prop 2.14 — quadrature: "To construct a square equal to a given rectilinear
figure A."  This is a CONSTRUCTION ("∃") proposition.

Modeling note:
  System E has NO general "rectilinear figure" type; area is only
  `Triangle.area`, and polygons are represented as SUMS of triangle areas
  (exactly as Prop 1.45 — which 2.14 cites — takes a quadrilateral as two
  `formTriangle`s and uses `area △ abd + area △ dbc`).  So "the given
  rectilinear figure A" is instantiated case-by-case.  We give the two
  simplest cases:
    proposition_14   — A is a TRIANGLE          (area = one Triangle.area)
    proposition_14'  — A is a QUADRILATERAL      (area = sum of two triangles,
                       given as two triangles, mirroring Prop 1.45's input)

  Conclusion: Euclid constructs only the SIDE of the square ("the square which
  can be described on EH"), so faithfully we exhibit a segment e─h whose square
  |e─h|*|e─h| equals the figure's area.  ("square on EH" = |EH|*|EH|, cf. 2.1/47.)

Proof strategy (the genuine Euclidean construction, mechanised):
  1.  Erect a perpendicular at a vertex of the figure to obtain a RIGHT ANGLE.
  2.  Apply Prop 1.42 / Prop 1.45 with that right angle: this produces a
      PARALLELOGRAM with a right angle (= a RECTANGLE) whose area equals the
      figure's area.  `rectangle_area` then gives its area as a product of two
      side lengths  p·q.
  3.  `helper_14_product` lays p and q out collinearly and erects the
      perpendicular up to the semicircle on their sum (`helper_14_geomean`),
      yielding a segment whose square equals p·q — i.e. the figure's area.
-/

-- To construct a square equal to a given rectilinear figure. Let $A$ be the given rectilinear figure. So it is required to construct a square equal to the rectilinear figure $A$. [Case: A is a triangle.] [Thus, a square---(namely), that (which) can be described on $EH$---has been constructed, equal to the given rectilinear figure $A$.]
theorem proposition_14 : ∀ (a b c : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:c :=
by
  euclid_intros
  -- (1) right angle ∠ p:a:b at vertex a
  euclid_apply (proposition_11'' a b AB) as p
  euclid_apply (line_from_points a p) as AP
  -- (2) rectangle (parallelogram with that right angle) equal to △ a:b:c
  euclid_apply (proposition_42 a b c p a b AB BC CA AP AB) as (f, g, e2, c', FG, EC, EF, CG)
  euclid_apply (rectangle_area f g e2 c' FG EC EF CG)
  -- now  |f─g| · |f─e2|  =  area △ a:b:c
  -- (3) geometric-mean construction on the two side lengths
  euclid_apply (helper_14_product f g e2 FG EF) as hh
  use g, hh
  euclid_finish

-- To construct a square equal to a given rectilinear figure. [Case: A is a quadrilateral, given as the two triangles a:b:d and d:b:c sharing diagonal BD, with a, c on opposite sides of BD (cf. Prop 1.45's input).]
theorem proposition_14' : ∀ (a b c d : Point) (AB BC CD AD DB : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:d + Triangle.area △ d:b:c :=
by
  euclid_intros
  -- (1) right angle ∠ p:a:b at vertex a
  euclid_apply (proposition_11'' a b AB) as p
  euclid_apply (line_from_points a p) as AP
  -- (2) Prop 1.45: parallelogram with that right angle (= rectangle) equal to the quadrilateral
  euclid_apply (proposition_45 a b c d p a b AB BC CD AD DB AP AB) as (f, l, k, m, FL, KM, FK, LM)
  euclid_apply (rectangle_area f l k m FL KM FK LM)
  -- now  |f─l| · |f─k|  =  area △ a:b:d + area △ d:b:c
  -- (3) geometric-mean construction on the two side lengths
  euclid_apply (helper_14_product f l k FL FK) as hh
  use l, hh
  euclid_finish

end Elements.Book2
