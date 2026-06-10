import SystemE
import Book.Prop03
import Book.Prop10
import Book.Prop11
import Book.Prop42
import Book.Prop45
import Book.Prop47

namespace Elements.Book2

open Elements.Book1

/--
Helper for `proposition_14` (quadrature).  The geometric-mean / "square root"
construction: given `b ─ e ─ f` collinear (e between b and f), the segment
`e─h` erected perpendicular at `e` up to the semicircle on diameter `bf`
satisfies `|e─h|² = |b─e|·|e─f|`.

Strategy:
  g  = midpoint of bf            (Prop 1.10), so |bg| = |gf| =: r.
  α  = circle centre g, radius gb (so b,f are on α).
  f0 = perpendicular to BF at e   (Prop 1.11), EH = line e f0.
  e is inside α (between two points of α) ⇒ EH meets α at some h.
  |gh| = |gb| = r  (h on α).  Right angle ∠g:e:h (BF ⟂ EH at e).
  Pythagoras (Prop 1.47) on △g:e:h:  |eh|² = |gh|² − |ge|² = r² − |ge|².
  Difference of squares (g midpoint, e between b f):  r² − |ge|² = |be|·|ef|.
-/
theorem helper_14_geomean : ∀ (b e f : Point) (BF : Line),
  distinctPointsOnLine b f BF ∧ between b e f →
  ∃ (h : Point), |(e─h)| * |(e─h)| = |(b─e)| * |(e─f)| :=
by
  euclid_intros
  -- midpoint g of bf
  euclid_apply (proposition_10 b f BF) as g
  -- circle centre g through b ; f is on it too
  euclid_apply (circle_from_points g b) as α
  euclid_apply (point_on_circle_if g b f α)
  -- e is inside the circle (strictly between two points of α)
  euclid_apply (circle_points_between b f e α)
  -- perpendicular to BF at e
  euclid_apply (proposition_11 b f e BF) as f0
  euclid_apply (line_from_points e f0) as EH
  -- the perpendicular through e (interior point) meets the circle
  euclid_apply (intersection_circle_line_2 e α EH)
  euclid_apply (intersections_circle_line α EH) as (h, h')
  -- h on circle ⇒ |gh| = |gb| = r
  euclid_apply (point_on_circle_onlyif g b h α)
  use h
  -- now purely length/angle reasoning
  euclid_apply (line_from_points g h) as GH
  by_cases (e = g)
  · -- e = g : e is the centre, |eh| = r, and |be|·|ef| = r²
    euclid_finish
  · -- e ≠ g.  Decompose: right angle at e ⇒ Pythagoras ⇒ difference of squares.
    -- (1) ∠ g:e:h is right: g lies on BF, the perpendicular EH meets BF at e at ∟.
    have hperp : (∠ g:e:h : ℝ) = ∟ := by euclid_finish
    -- (2) g,e,h form a triangle (h is off BF, e ≠ g).
    euclid_apply (proposition_47 e g h BF GH EH)
    -- now in context: |g─h|² = |g─e|² + |e─h|²   (Pythagoras, right angle at e)
    -- and  |g─h| = |g─b|   (h, b both on α centred at g)
    -- (3) difference of squares: |gb|² − |ge|² = |be|·|ef|  (g midpoint of bf).
    euclid_finish

/--
Helper for `proposition_14`.  Given two segments `f─g` (length p) and `f─e`
(length q), lay them out *collinearly* and produce a point `h` with
`|g─h|² = p·q = |f─g|·|f─e|`.

Strategy:
  Along line FG, beyond g, mark f₀ with `|g─f₀| = |f─e| = q` (Prop 1.3, after
  extending FG far enough).  Then `f ─ g ─ f₀` is collinear with `|f─g| = p`,
  `|g─f₀| = q`, so `helper_14_geomean f g f₀ FG` gives `h` with
  `|g─h|² = |f─g|·|g─f₀| = p·q`.
-/
theorem helper_14_product : ∀ (f g e : Point) (FG FE : Line),
  distinctPointsOnLine f g FG ∧ distinctPointsOnLine f e FE →
  ∃ (h : Point), |(g─h)| * |(g─h)| = |(f─g)| * |(f─e)| :=
by
  euclid_intros
  -- extend FG beyond g far enough to cut off a length |f─e|
  euclid_apply (extend_point_longer FG f g (f─e)) as x
  -- cut off f₀ on (g,x) with |g─f₀| = |f─e|
  euclid_apply (proposition_3 g x f e FG FE) as f0
  -- f ─ g ─ f₀ collinear, distinct
  have hbet : between f g f0 := by euclid_finish
  euclid_apply (helper_14_geomean f g f0 FG) as hh
  use hh
  -- |g─hh|² = |f─g|·|g─f₀|  and  |g─f₀| = |f─e|
  euclid_finish

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
