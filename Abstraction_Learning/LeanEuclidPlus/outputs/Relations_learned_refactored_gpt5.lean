import SystemE.Theory.Relations


/-!
Refactored Extension: Canonical geometric relations and reusable combinators for 2D Euclidean Geometry.

Design principles:
- No external imports.
- No new types; only use the DSL primitives.
- Quantifier-free and no disjunctions.
- All new definitions are registered with `[simp]`.
- Prefer the opaque constant `∟` for right angles.
- Remove redundant aliases and over-specific APIs; keep general, reusable predicates.

Highlights:
- List-based betweenness chain and "three-or-more" guard.
- Sides/opposing-sides combinators for lists of points.
- Parallel, supplementary angles, perpendicularity at a witness point.
- Non-collinearity via triangle area.
- Equal-length ratios, triangle angle sum, triangle similarity (generalized).
- Simplified convex quadrilateral (no redundant conditions).
- Diagonals of an ordered quadruple.
- General angle bisector at a vertex (with side and bisector lines).
- Triangle congruence (generalized).
- Side selectors for triangles and "share a side" witness.
- Equilateral and isosceles triangles (generalized).
- Lines cutting triangle sides and their parallel variants.
-/

-- List-based helpers

/-- Chain of betweenness along a list:
for a::b::c::rest, requires `between a b c` and then recurses on `b::c::rest`. -/
@[simp]
def betweennessChain (pts : List Point) : Prop :=
  match pts with
  | a :: b :: c :: rest => between a b c ∧ betweennessChain (b :: c :: rest)
  | _                   => True

/-- The list has length at least three points. -/
@[simp]
def hasAtLeastThree (pts : List Point) : Prop :=
  match pts with
  | _ :: _ :: _ :: _ => True   -- 4 or more
  | _ :: _ :: _      => True   -- exactly 3
  | _                => False

/-- No point in a list lies on a given line. -/
@[simp]
def noneOnLine (pts : List Point) (L : Line) : Prop :=
  match pts with
  | []       => True
  | x :: xs  => ¬ x.onLine L ∧ noneOnLine xs L

/-- All points in `ys` are on the side of line `L` opposite to point `x`. -/
@[simp]
def allOpposingSidesToPoint (x : Point) (ys : List Point) (L : Line) : Prop :=
  match ys with
  | []      => True
  | y :: ys => x.opposingSides y L ∧ allOpposingSidesToPoint x ys L

/-- For two lists of points `xs` and `ys`, every cross-pair (x in xs, y in ys) lies on opposing sides of `L`. -/
@[simp]
def pairwiseAcrossOpposing (xs ys : List Point) (L : Line) : Prop :=
  match xs with
  | []      => True
  | x :: xs => allOpposingSidesToPoint x ys L ∧ pairwiseAcrossOpposing xs ys L


-- Basic relations

/-- Two distinct lines `L` and `M` intersect at point `i`. -/
@[simp]
def twoDistinctLinesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  L ≠ M ∧ i.onLine L ∧ i.onLine M ∧ L.intersectsLine M

/-- A list of points is sequentially aligned (ordered collinear chain via betweenness).
No explicit line or pairwise-distinctness requirement is added; betweenness provides
the needed distinctness and collinearity for each consecutive triple. -/
@[simp]
def sequentiallyAligned (pts : List Point) : Prop :=
  betweennessChain pts

/-- Sequential alignment with at least three points. -/
@[simp]
def sequentiallyAlignedThreeOrMore (pts : List Point) : Prop :=
  hasAtLeastThree pts ∧ betweennessChain pts

/-- Two sets (lists) of points lie on opposing sides of a line `L`:
- no point from either list is on `L`;
- every cross-pair across the two lists is on opposite sides of `L`. -/
@[simp]
def twoSetsOpposingSidesOnLine (xs ys : List Point) (L : Line) : Prop :=
  noneOnLine xs L ∧ noneOnLine ys L ∧ pairwiseAcrossOpposing xs ys L

/-- Two angles ∠ a:b:c and ∠ d:e:f are supplementary iff their measures sum to ∟ + ∟. -/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = ∟ + ∟

/-- Two lines are parallel if they are distinct and do not intersect. -/
@[simp]
def parallel (L M : Line) : Prop :=
  L ≠ M ∧ ¬ L.intersectsLine M


-- Non-collinearity

/-- Three points are non-collinear iff the area of the triangle they form is nonzero. -/
@[simp]
def nonCollinearPoints (a b c : Point) : Prop :=
  Triangle.area (△ a:b:c) ≠ 0


-- Segments to opposite sides of a triangle

/-- A segment `SP` connects vertex `v` to a point `p` on the opposite side `s1s2` of a triangle,
witnessed by `between s1 p s2`. -/
@[simp]
def segmentFromVertexToOppositeSide (v s1 s2 p : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints v p ∧ between s1 p s2


-- Midpoints

namespace Point

/-- Point `m` is the midpoint of segment AB iff:
- `m` lies between `a` and `b` (hence all three are distinct and collinear);
- the distances from `m` to the endpoints are equal. -/
@[simp]
def isMidpointOf (m a b : Point) : Prop :=
  between a m b ∧ |(a─m)| = |(m─b)|

/-- Same as `isMidpointOf m a b`, with an explicit segment witness `SP = [a,b]`. -/
@[simp]
def isMidpointOfSegmentEndpoints (m a b : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints a b ∧ isMidpointOf m a b

/-- Point `p` lies on the extension of segment `AB` beyond endpoint `B`
iff `B` is between `A` and `P`. -/
@[simp]
def onExtensionBeyondB (p a b : Point) : Prop :=
  between a b p

/-- Point `p` lies on the extension of segment `AB` beyond endpoint `A`
iff `A` is between `B` and `P`. -/
@[simp]
def onExtensionBeyondA (p a b : Point) : Prop :=
  between b a p

end Point


-- Congruent segments (endpoint-based)

/-- Segments `AB` and `CD` are congruent iff their lengths are equal. -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|


-- Perpendicular lines

/-- Lines `L` and `M` are perpendicular, witnessed at point `i` with points `a` on `L`
and `c` on `M`, iff:
- `L` and `M` intersect;
- `a,i,c` form a rectilinear angle with sides on `L` and `M`;
- the angle ∠ AIC is a right angle (∟). -/
@[simp]
def perpendicularAt (L M : Line) (i a c : Point) : Prop :=
  L.intersectsLine M ∧ formRectilinearAngle a i c L M ∧ (∠ a:i:c) = ∟


-- Ratios and angle sums

/-- Equality of two ratios of segment lengths given by endpoints:
(|AB| / |CD|) = (|EF| / |GH|). -/
@[simp]
def equalLengthRatios (a b c d e f g h : Point) : Prop :=
  (|(a─b)| / |(c─d)|) = (|(e─f)| / |(g─h)|)

/-- For a non-degenerate triangle `ABC`, the sum of its interior angles is ∟ + ∟. -/
@[simp]
def triangleAngleSum (a b c : Point) : Prop :=
  nonCollinearPoints a b c ∧
  ((∠ b:a:c) + (∠ a:b:c) + (∠ a:c:b) = ∟ + ∟)


-- Triangle similarity and congruence (generalized, no non-degeneracy assumption)

/-- Triangles `ABC` and `DEF` are similar iff:
- all three corresponding angles are equal:
    ∠ BAC = ∠ EDF, ∠ ABC = ∠ DEF, ∠ ACB = ∠ DFE;
- corresponding sides are equally proportional:
    |AB|/|DE| = |BC|/|EF| and |BC|/|EF| = |CA|/|FD|. -/
@[simp]
def trianglesSimilar (a b c d e f : Point) : Prop :=
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  (|(a─b)| / |(d─e)|) = (|(b─c)| / |(e─f)|) ∧
  (|(b─c)| / |(e─f)|) = (|(c─a)| / |(f─d)|)

/-- Triangles `ABC` and `DEF` are congruent iff:
- all three corresponding angles are equal;
- all three corresponding sides are equal in length. -/
@[simp]
def trianglesCongruent (a b c d e f : Point) : Prop :=
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  (|(a─b)|) = (|(d─e)|) ∧
  (|(b─c)|) = (|(e─f)|) ∧
  (|(c─a)|) = (|(f─d)|)


-- Convex quadrilateral (simplified, canonical)

 /-- Four points `a,b,c,d` with side-lines `AB,BC,CD,DA` form a convex quadrilateral iff:
- consecutive vertices lie on their side lines with distinct endpoints;
- for each side line, the two nonincident vertices lie on the same side of that line.

No extra distinctness, non-collinearity, or intersection requirements are added; these
are ensured by the existing primitives (`distinctPointsOnLine` and `sameSide`). -/
@[simp]
def formConvexQuadrilateral (a b c d : Point) (AB BC CD DA : Line) : Prop :=
  distinctPointsOnLine a b AB ∧
  distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧
  distinctPointsOnLine d a DA ∧
  c.sameSide d AB ∧
  d.sameSide a BC ∧
  a.sameSide b CD ∧
  b.sameSide c DA


-- Diagonals of an ordered quadruple

/-- `SP` is the diagonal AC of the ordered quadruple (a, b, c, d). -/
@[simp]
def diagonalACOfQuadrilateral (a _b c _d : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints a c

/-- `SP` is the diagonal BD of the ordered quadruple (a, b, c, d). -/
@[simp]
def diagonalBDOfQuadrilateral (_a b _c d : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints b d


-- General angle bisector at a vertex

/-- Segment `BP` bisects angle ABC at vertex `b`. The user provides side lines `AB`, `BC`
and the carrier line `BP` for the bisecting segment. Requirements:
- `a,b` lie on `AB`; `b,c` lie on `BC`; `b,p` lie on `BP`;
- interior is witnessed by same-side constraints:
    `a` and `p` same side of `BC`, and `c` and `p` same side of `AB`;
- sub-angles are equal: ∠ ABP = ∠ PBC;
- `SP` is the segment with endpoints `b` and `p`. -/
@[simp]
def segmentBisectsAngleAtVertex (a b c p : Point) (SP : Segment)
    (AB BC BP : Line) : Prop :=
  a.onLine AB ∧ b.onLine AB ∧
  b.onLine BC ∧ c.onLine BC ∧
  b.onLine BP ∧ p.onLine BP ∧
  a.sameSide p BC ∧
  c.sameSide p AB ∧
  (∠ a:b:p) = (∠ p:b:c) ∧
  SP = Segment.endpoints b p


-- Triangle side selectors and "share-a-side" witness

namespace Triangle

/-- The side AB of triangle `ABC` as a segment. -/
@[simp]
def sideAB (a b : Point) (_c : Point) : Segment :=
  Segment.endpoints a b

/-- The side BC of triangle `ABC` as a segment. -/
@[simp]
def sideBC (_a : Point) (b c : Point) : Segment :=
  Segment.endpoints b c

/-- The side CA of triangle `ABC` as a segment. -/
@[simp]
def sideCA (a : Point) (_b : Point) (c : Point) : Segment :=
  Segment.endpoints c a

end Triangle

/-- Two triangles `ABC` and `DEF` share a common side when the selected side segments are equal.
Typical side selectors are `Triangle.sideAB`, `Triangle.sideBC`, or `Triangle.sideCA`. -/
@[simp]
def trianglesShareSideBy
    (sel₁ : Point → Point → Point → Segment)
    (sel₂ : Point → Point → Point → Segment)
    (a b c d e f : Point) : Prop :=
  sel₁ a b c = sel₂ d e f


-- Equilateral and isosceles triangles (generalized)

/-- Triangle `ABC` is equilateral iff `|AB| = |BC| = |CA|` (encoded as two equalities). -/
@[simp]
def equilateralTriangle (a b c : Point) : Prop :=
  |(a─b)| = |(b─c)| ∧
  |(b─c)| = |(c─a)|

/-- Triangle `ABC` is isosceles at vertex `A` iff `|AB| = |AC|`. -/
@[simp]
def isoscelesAtA (a b c : Point) : Prop :=
  |(a─b)| = |(a─c)|

/-- Triangle `ABC` is isosceles at vertex `B` iff `|BA| = |BC|`. -/
@[simp]
def isoscelesAtB (a b c : Point) : Prop :=
  |(b─a)| = |(b─c)|

/-- Triangle `ABC` is isosceles at vertex `C` iff `|CA| = |CB|`. -/
@[simp]
def isoscelesAtC (a b c : Point) : Prop :=
  |(c─a)| = |(c─b)|


-- Lines cutting triangle sides (simplified, canonical)

/-- Line `L` intersects sides `AB` and `AC` of triangle `ABC` at points `p` and `q` respectively:
- `ABC` is formed by lines `AB`, `BC`, `CA`;
- `A-p-B` and `C-q-A` betweenness;
- both `p` and `q` lie on `L`. -/
@[simp]
def lineCutsTriangleOnABandACAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p b ∧
  between c q a ∧
  p.onLine L ∧ q.onLine L

/-- Line `L` intersects sides `AB` and `BC` of triangle `ABC` at points `p` and `q` respectively:
- `ABC` is formed by lines `AB`, `BC`, `CA`;
- `A-p-B` and `B-q-C` betweenness;
- both `p` and `q` lie on `L`. -/
@[simp]
def lineCutsTriangleOnABandBCAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p b ∧
  between b q c ∧
  p.onLine L ∧ q.onLine L

/-- Line `L` intersects sides `AC` and `BC` of triangle `ABC` at points `p` and `q` respectively:
- `ABC` is formed by lines `AB`, `BC`, `CA`;
- `C-p-A` and `B-q-C` betweenness;
- both `p` and `q` lie on `L`. -/
@[simp]
def lineCutsTriangleOnACandBCAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between c p a ∧
  between b q c ∧
  p.onLine L ∧ q.onLine L


-- Parallel variants

/-- Line `L` cuts sides `AB` and `AC` at `p` and `q` and is parallel to `BC`. -/
@[simp]
def lineCutsABandACParallelBC
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p b ∧
  between c q a ∧
  p.onLine L ∧ q.onLine L ∧
  parallel L BC

/-- Line `L` cuts sides `AB` and `BC` at `p` and `q` and is parallel to `CA`. -/
@[simp]
def lineCutsABandBCParallelCA
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p b ∧
  between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  parallel L CA

/-- Line `L` cuts sides `AC` and `BC` at `p` and `q` and is parallel to `AB`. -/
@[simp]
def lineCutsACandBCParallelAB
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between c p a ∧
  between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  parallel L AB