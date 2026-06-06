import SystemE
-- Add dependencies as needed, e.g.:
--   import Book.Prop47      -- a Book 1 result (lib `Book`)
--   import Book2.Prop05     -- an earlier Book 2 result

namespace Elements.Book2

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
-/

-- To construct a square equal to a given rectilinear figure. Let $A$ be the given rectilinear figure. So it is required to construct a square equal to the rectilinear figure $A$. [Case: A is a triangle.] [Thus, a square---(namely), that (which) can be described on $EH$---has been constructed, equal to the given rectilinear figure $A$.]
theorem proposition_14 : ∀ (a b c : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:c :=
by
  sorry

-- To construct a square equal to a given rectilinear figure. [Case: A is a quadrilateral, given as the two triangles a:b:d and d:b:c sharing diagonal BD, with a, c on opposite sides of BD (cf. Prop 1.45's input).]
theorem proposition_14' : ∀ (a b c d : Point) (AB BC CD AD DB : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:d + Triangle.area △ d:b:c :=
by
  sorry

end Elements.Book2
