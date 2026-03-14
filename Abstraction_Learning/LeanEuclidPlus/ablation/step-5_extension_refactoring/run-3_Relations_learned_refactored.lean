import SystemE.Theory.Relations


/-!
Refactored extensions: quantifier-free, duplication-free additions for 2D Euclidean Geometry.

This file provides:
- Basic list combinators: allOnLine, betweennessChain, hasAtLeastThree.
- Intersections and sidedness: twoDistinctLinesIntersectAtPoint, opposing-sides list combinators.
- Alignment along a line: sequentiallyAlignedOnLine and the "three or more" variant.
- Angle and line relations: supplementaryAngles, parallel, perpendicularAt.
- Non-collinearity via area: nonCollinearPoints.
- Segments and midpoints: segmentLength, congruentSegments, Point.isMidpointOf.
- Angle bisector at a vertex: segmentBisectsAngleAtVertex.
- Extensions along a segment: Point.onExtensionBeyondA/B.
- Equal length ratios (endpoints and segment-based).
- Triangle relations: triangleAngleSum, trianglesSimilar, trianglesCongruent, equilateralTriangle, isosceles*.
- Quadrilaterals: formConvexQuadrilateral (minimal canonical form), diagonals AC and BD.
- Triangle sides and shared side witness: Triangle.sideAB/BC/CA and trianglesShareSideBy.
- Lines cutting triangle sides and parallel variants.

All definitions are quantifier-free, avoid disjunction, and are registered with @[simp].
-/


/-! Helpers: list-based combinators (quantifier-free) -/

/-- Every point in a list lies on a given line. -/
@[simp]
def allOnLine (pts : List Point) (L : Line) : Prop :=
  match pts with
  | []       => True
  | x :: xs  => x.onLine L ∧ allOnLine xs L

/-- Chain of betweenness along a list:
for a::b::c::rest, requires between a b c and then recurses on b::c::rest. -/
@[simp]
def betweennessChain (pts : List Point) : Prop :=
  match pts with
  | a :: b :: c :: rest => between a b c ∧ betweennessChain (b :: c :: rest)
  | _                   => True

/-- The list has length at least 3 (i.e., contains three or more points). -/
@[simp]
def hasAtLeastThree (pts : List Point) : Prop :=
  match pts with
  | _ :: _ :: _ :: _ => True
  | _ :: _ :: _      => True
  | _                => False


/-! Intersections and sidedness -/

/-- Two distinct lines L and M intersect at point i. -/
@[simp]
def twoDistinctLinesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  L ≠ M ∧ i.onLine L ∧ i.onLine M ∧ L.intersectsLine M

/-- All points in `ys` are on the side of line L opposite to point `x`. -/
@[simp]
def allOpposingSidesToPoint (x : Point) (ys : List Point) (L : Line) : Prop :=
  match ys with
  | []       => True
  | y :: ys  => x.opposingSides y L ∧ allOpposingSidesToPoint x ys L

/-- For two lists `xs` and `ys`, every cross-pair (x in xs, y in ys) lies on opposing sides of L. -/
@[simp]
def pairwiseAcrossOpposing (xs ys : List Point) (L : Line) : Prop :=
  match xs with
  | []       => True
  | x :: xs  => allOpposingSidesToPoint x ys L ∧ pairwiseAcrossOpposing xs ys L

/-- Two lists of points lie on opposing sides of a line L, witnessed crosswise. -/
@[simp]
def twoSetsOpposingSidesOnLine (xs ys : List Point) (L : Line) : Prop :=
  pairwiseAcrossOpposing xs ys L


/-! Sequential alignment on a line -/

/-- A list of points is sequentially aligned on line L if:
- all of them lie on L;
- consecutive triples satisfy a betweenness chain.

No explicit global pairwise-distinctness is imposed (between already carries
the necessary local distinctness and collinearity information). -/
@[simp]
def sequentiallyAlignedOnLine (pts : List Point) (L : Line) : Prop :=
  allOnLine pts L ∧ betweennessChain pts

/-- Enforces at least three points in addition to sequential alignment on L. -/
@[simp]
def sequentiallyAlignedThreeOrMore (pts : List Point) (L : Line) : Prop :=
  hasAtLeastThree pts ∧ sequentiallyAlignedOnLine pts L


/-! Angles and lines -/

/-- Angles ∠ a:b:c and ∠ d:e:f are supplementary iff their measures sum to ∟ + ∟. -/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = ∟ + ∟

/-- Two lines are parallel iff they are distinct and do not intersect. -/
@[simp]
def parallel (L M : Line) : Prop :=
  L ≠ M ∧ ¬ L.intersectsLine M

/-- Lines `L` and `M` are perpendicular, witnessed at point `i` with points `a` on `L`
and `c` on `M`, iff:
- `L` and `M` intersect;
- `a,i,c` form a rectilinear angle with sides on `L` and `M`;
- the angle ∠ AIC is a right angle (∟). -/
@[simp]
def perpendicularAt (L M : Line) (i a c : Point) : Prop :=
  L.intersectsLine M ∧ formRectilinearAngle a i c L M ∧ (∠ a:i:c) = ∟


/-! Non-collinearity via area -/

/-- Three points are non-collinear iff the area of △ABC is nonzero. -/
@[simp]
def nonCollinearPoints (a b c : Point) : Prop :=
  Triangle.area (△ a:b:c) ≠ 0


/-! Segments and midpoints -/

/-- The length of a segment, obtained by destructing its endpoints. -/
@[simp] noncomputable
def segmentLength (SP : Segment) : ℝ :=
  match SP with
  | Segment.endpoints a b => |(a─b)|

/-- Segments `AB` and `CD` are congruent iff their lengths are equal. -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

namespace Point

/-- Point `m` is the midpoint of segment AB iff:
- `m` lies between `a` and `b` (hence all three are distinct and collinear);
- the distances from `m` to the endpoints are equal. -/
@[simp]
def isMidpointOf (m a b : Point) : Prop :=
  between a m b ∧ |(a─m)| = |(m─b)|

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


/-! Angle bisectors -/

/-- Segment `BP` bisects angle ABC at vertex `b`. The user provides side lines `AB`, `BC`
and the carrier line `BP` for the segment. We require:
- `a` and `b` lie on `AB`;
- `b` and `c` lie on `BC`;
- `b` and `p` lie on `BP`;
- `p` is interior to the angle at `b` via same-side constraints:
    `a` and `p` are on the same side of `BC`, and
    `c` and `p` are on the same side of `AB`;
- the two sub-angles have equal measure: ∠ ABP = ∠ PBC;
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


/-! Equal ratios of lengths -/

/-- Equality of two ratios of lengths given by endpoints:
(|AB| / |CD|) = (|EF| / |GH|). -/
@[simp]
def equalLengthRatios (a b c d e f g h : Point) : Prop :=
  (|(a─b)| / |(c─d)|) = (|(e─f)| / |(g─h)|)

/-- Equality of two ratios of segment lengths using segment witnesses:
length(SP1)/length(SP2) = length(SP3)/length(SP4). -/
@[simp] noncomputable
def equalLengthRatiosBySegments (SP1 SP2 SP3 SP4 : Segment) : Prop :=
  segmentLength SP1 / segmentLength SP2 = segmentLength SP3 / segmentLength SP4


/-! Triangle: angle sum, similarity, congruence, and side-class properties -/

/-- The three angles around points A, B, C sum to ∟ + ∟. -/
@[simp]
def triangleAngleSum (a b c : Point) : Prop :=
  (∠ b:a:c) + (∠ a:b:c) + (∠ a:c:b) = ∟ + ∟

/-- Triangles `ABC` and `DEF` are similar if all corresponding angles are equal and
corresponding sides are equally proportional (encoded by a chain of two equalities). -/
@[simp]
def trianglesSimilar (a b c d e f : Point) : Prop :=
  -- angle correspondences
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  -- side-ratio correspondences (chained)
  (|(a─b)| / |(d─e)|) = (|(b─c)| / |(e─f)|) ∧
  (|(b─c)| / |(e─f)|) = (|(c─a)| / |(f─d)|)

/-- Triangles `ABC` and `DEF` are congruent iff all corresponding angles are equal
and all corresponding sides are equal in length. -/
@[simp]
def trianglesCongruent (a b c d e f : Point) : Prop :=
  -- angle correspondences
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  -- side correspondences
  |(a─b)| = |(d─e)| ∧
  |(b─c)| = |(e─f)| ∧
  |(c─a)| = |(f─d)|

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

namespace Triangle

/-- The side AB of triangle `ABC` as a segment. -/
@[simp]
def sideAB (a b : Point) (_c : Point) : Segment :=
  Segment.endpoints a b

/-- The side BC of triangle `ABC` as a segment. -/
@[simp]
def sideBC (_a : Point) (b c : Point) : Segment :=
  Segment.endpoints b c

/-- The side CA of triangle `ABC` as a segment (ordered CA). -/
@[simp]
def sideCA (a : Point) (_b : Point) (c : Point) : Segment :=
  Segment.endpoints c a

end Triangle

/-- Two triangles `ABC` and `DEF` share a common side, witnessed by choosing side-selectors
for each triangle, when the selected side segments are equal. Typical side selectors are
`Triangle.sideAB`, `Triangle.sideBC`, or `Triangle.sideCA`. -/
@[simp]
def trianglesShareSideBy
    (sel₁ : Point → Point → Point → Segment)
    (sel₂ : Point → Point → Point → Segment)
    (a b c d e f : Point) : Prop :=
  sel₁ a b c = sel₂ d e f


/-! Quadrilaterals -/

/-- Four points `a,b,c,d` with side-lines `AB,BC,CD,DA` form a convex quadrilateral iff:
- consecutive vertices lie on their side lines with distinct endpoints;
- for each side line, the two nonincident vertices lie on the same side of that line
  (this encodes convexity and non-self-intersection).

The order is strictly respected: `a-b` on `AB`, `b-c` on `BC`, `c-d` on `CD`, `d-a` on `DA`. -/
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

/-- `SP` is the diagonal AC of the ordered quadruple (a, b, c, d). -/
@[simp]
def diagonalACOfQuadrilateral (a _b c _d : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints a c

/-- `SP` is the diagonal BD of the ordered quadruple (a, b, c, d). -/
@[simp]
def diagonalBDOfQuadrilateral (_a b _c d : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints b d


/-! Lines cutting triangle sides -/

/-- Line `L` intersects sides `AB` and `AC` of triangle `ABC` at points `p` and `q` respectively:
- `ABC` is formed by lines `AB`, `BC`, `CA`;
- `p` lies on `AB` with `A-p-B` betweenness;
- `q` lies on `CA` with `C-q-A` betweenness;
- both `p` and `q` lie on `L`. -/
@[simp]
def lineCutsTriangleOnABandACAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine CA ∧ between c q a ∧
  p.onLine L ∧ q.onLine L

/-- Line `L` intersects sides `AB` and `BC` of triangle `ABC` at points `p` and `q` respectively:
- `ABC` is formed by lines `AB`, `BC`, `CA`;
- `p` lies on `AB` with `A-p-B` betweenness;
- `q` lies on `BC` with `B-q-C` betweenness;
- both `p` and `q` lie on `L`. -/
@[simp]
def lineCutsTriangleOnABandBCAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L

/-- Line `L` intersects sides `AC` and `BC` of triangle `ABC` at points `p` and `q` respectively:
- `ABC` is formed by lines `AB`, `BC`, `CA`;
- `p` lies on `CA` with `C-p-A` betweenness;
- `q` lies on `BC` with `B-q-C` betweenness;
- both `p` and `q` lie on `L`. -/
@[simp]
def lineCutsTriangleOnACandBCAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧ between c p a ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L


/-! Parallel variants -/

/-- Line `L` intersects sides `AB` and `AC` and is parallel to `BC`. -/
@[simp]
def lineCutsABandACParallelBC
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine CA ∧ between c q a ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine AB ∧ L.intersectsLine CA ∧
  parallel L BC

/-- Line `L` intersects sides `AB` and `BC` and is parallel to `CA`. -/
@[simp]
def lineCutsABandBCParallelCA
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine AB ∧ L.intersectsLine BC ∧
  parallel L CA

/-- Line `L` intersects sides `AC` and `BC` and is parallel to `AB`. -/
@[simp]
def lineCutsACandBCParallelAB
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧ between c p a ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine CA ∧ L.intersectsLine BC ∧
  parallel L AB