import SystemE.Theory.Relations


/-!
Extension: Additional geometric relations and list-based combinators for 2D Euclidean Geometry.

This file introduces:
1. twoDistinctLinesIntersectAtPoint: two distinct lines intersecting at a specified point.
2. sequentiallyAlignedOnLine / sequentiallyAlignedThreeOrMore: a list of points aligned and ordered on a line (three or more).
3. twoSetsOpposingSidesOnLine: two lists of points lying on opposing sides of a line.
4. supplementaryAngles: two angles are supplementary (sum to a straight angle, i.e., ∟ + ∟).
5. parallel: two lines are parallel (distinct and non-intersecting).

Auxiliary list-based helpers are provided to express quantifier-free "for all in a list" style properties.
All definitions are quantifier-free and avoid disjunction, in accordance with the DSL constraints.
-/

/-! Helper: point-list combinators (quantifier-free "for all in list" style) -/

/-- A point is distinct from every element in a list of points. -/
@[simp]
def distinctFromList (x : Point) (ys : List Point) : Prop :=
  match ys with
  | []      => True
  | y :: ys => x ≠ y ∧ distinctFromList x ys

/-- A list of points is pairwise distinct (no duplicates). -/
@[simp]
def pairwiseDistinct (pts : List Point) : Prop :=
  match pts with
  | []       => True
  | x :: xs  => distinctFromList x xs ∧ pairwiseDistinct xs

/-- Every point in a list lies on a given line. -/
@[simp]
def allOnLine (pts : List Point) (L : Line) : Prop :=
  match pts with
  | []       => True
  | x :: xs  => x.onLine L ∧ allOnLine xs L

/-- No point in a list lies on a given line. -/
@[simp]
def noneOnLine (pts : List Point) (L : Line) : Prop :=
  match pts with
  | []       => True
  | x :: xs  => ¬ x.onLine L ∧ noneOnLine xs L

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
  | _ :: _ :: _ :: _ => True   -- 4 or more
  | _ :: _ :: _      => True   -- exactly 3
  | _                => False


/-! 1. Two distinct lines intersecting at a specified point -/

/-- Two distinct lines L and M intersect at point i:
- L and M are distinct;
- i lies on both L and M;
- L and M intersect (as a compatibility link to the DSL primitive).
-/
@[simp]
def twoDistinctLinesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  L ≠ M ∧ i.onLine L ∧ i.onLine M ∧ L.intersectsLine M


/-! 2. Three or more distinct points being sequentially aligned on a line -/

/-- A (possibly short) list of points is sequentially aligned on line L:
- all listed points lie on L;
- the list is pairwise distinct;
- consecutive triples form a chain of "between" relations.

Note: This definition by itself imposes no lower bound on the number of points.
Use `sequentiallyAlignedThreeOrMore` to enforce "three or more".
-/
@[simp]
def sequentiallyAlignedOnLine (pts : List Point) (L : Line) : Prop :=
  allOnLine pts L ∧ pairwiseDistinct pts ∧ betweennessChain pts

/-- "Three or more distinct points being sequentially aligned on a line":
enforces at least three points in addition to `sequentiallyAlignedOnLine`.
-/
@[simp]
def sequentiallyAlignedThreeOrMore (pts : List Point) (L : Line) : Prop :=
  hasAtLeastThree pts ∧ sequentiallyAlignedOnLine pts L


/-! 3. Two sets (lists) of points lying on opposing sides of a line -/

/-- All points in `ys` are on the side of line L opposite to point `x`. -/
@[simp]
def allOpposingSidesToPoint (x : Point) (ys : List Point) (L : Line) : Prop :=
  match ys with
  | []       => True
  | y :: ys  => x.opposingSides y L ∧ allOpposingSidesToPoint x ys L

/-- For two lists of points `xs` and `ys`, every cross-pair (x in xs, y in ys) lies on opposing sides of L. -/
@[simp]
def pairwiseAcrossOpposing (xs ys : List Point) (L : Line) : Prop :=
  match xs with
  | []       => True
  | x :: xs  => allOpposingSidesToPoint x ys L ∧ pairwiseAcrossOpposing xs ys L

/-- Two sets (lists) of points lie on opposing sides of a line L:
- no point from either list is on L (explicitly enforced);
- every cross-pair (x in xs, y in ys) are on opposite sides of L. -/
@[simp]
def twoSetsOpposingSidesOnLine (xs ys : List Point) (L : Line) : Prop :=
  noneOnLine xs L ∧ noneOnLine ys L ∧ pairwiseAcrossOpposing xs ys L


/-! 4. Two angles being supplementary -/

/-- The two angles ∠ a:b:c and ∠ d:e:f are supplementary iff their measures sum to ∟ + ∟. -/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = ∟ + ∟


/-! 5. Two lines being parallel -/

/-- Two lines are parallel if they are distinct and do not intersect. -/
@[simp]
def parallel (L M : Line) : Prop :=
  L ≠ M ∧ ¬ L.intersectsLine M


-- Extension: Congruent angles, non-collinear-point triangles, shared-vertex triangles,
-- triangle-vertex angles, and vertex-to-opposite-side segments.

@[simp]
def pairwiseDistinct3 (a b c : Point) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ a

-- 1. Two angles being congruent (equal measure)
@[simp]
def congruentAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) = (∠ d:e:f)

-- 2. A triangle defined by three non-collinear points
@[simp]
def nonCollinearPoints (a b c : Point) : Prop :=
  Triangle.area (△ a:b:c) ≠ 0

@[simp]
def pointsDefineTriangle (a b c : Point) : Prop :=
  pairwiseDistinct3 a b c ∧ nonCollinearPoints a b c

-- 3. Two triangles sharing a common vertex (explicitly specified point equality)
-- The user must pass the specific vertices; no disjunctions or quantifiers are used.
@[simp]
def trianglesShareVertexBy (v1 v2 : Point) : Prop :=
  v1 = v2

-- 4. Angles at the vertices of a triangle
namespace Triangle

@[simp]
def angleAtA (a b c : Point) : ℝ :=
  (∠ b:a:c)

@[simp]
def angleAtB (a b c : Point) : ℝ :=
  (∠ a:b:c)

@[simp]
def angleAtC (a b c : Point) : ℝ :=
  (∠ a:c:b)

end Triangle

-- 5. A line segment from a vertex of a triangle to a point on the opposite side
@[simp]
def segmentFromVertexToOppositeSide (v s1 s2 p : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints v p ∧ between s1 p s2

@[simp]
def segmentFromAtoOppositeSide (a b c p : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints a p ∧ between b p c

@[simp]
def segmentFromBtoOppositeSide (a b c p : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints b p ∧ between c p a

@[simp]
def segmentFromCtoOppositeSide (a b c p : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints c p ∧ between a p b


/-!
Extension: Midpoints, angle-bisecting segments, extension points beyond endpoints,
congruent segments, and perpendicular lines (witnessed formulation).

All definitions are quantifier-free, avoid disjunctions, and follow the DSL style.
-/

-- 1. A point being the midpoint of a line segment (AB)
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

end Point


-- 2. A line segment bisecting an angle at a vertex of a triangle

/-- Segment `AP` bisects the angle at vertex `A` of triangle `ABC`:
- `a,b,c` form a non-degenerate triangle (non-collinear and pairwise distinct);
- `SP` is the segment from `a` to `p`;
- the two sub-angles at `A`, namely ∠ BAP and ∠ PAC, are equal. -/
@[simp]
def segmentBisectsAngleAtA (a b c p : Point) (SP : Segment) : Prop :=
  pointsDefineTriangle a b c ∧
  SP = Segment.endpoints a p ∧
  (∠ b:a:p) = (∠ p:a:c)

/-- Segment `BP` bisects the angle at vertex `B` of triangle `ABC`:
- `a,b,c` form a non-degenerate triangle;
- `SP` is the segment from `b` to `p`;
- the two sub-angles at `B`, namely ∠ ABP and ∠ PBC, are equal. -/
@[simp]
def segmentBisectsAngleAtB (a b c p : Point) (SP : Segment) : Prop :=
  pointsDefineTriangle a b c ∧
  SP = Segment.endpoints b p ∧
  (∠ a:b:p) = (∠ p:b:c)

/-- Segment `CP` bisects the angle at vertex `C` of triangle `ABC`:
- `a,b,c` form a non-degenerate triangle;
- `SP` is the segment from `c` to `p`;
- the two sub-angles at `C`, namely ∠ ACP and ∠ PCB, are equal. -/
@[simp]
def segmentBisectsAngleAtC (a b c p : Point) (SP : Segment) : Prop :=
  pointsDefineTriangle a b c ∧
  SP = Segment.endpoints c p ∧
  (∠ a:c:p) = (∠ p:c:b)


-- 3. A point lying on the extension of a line segment beyond an endpoint
namespace Point

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


-- 4. Two line segments being congruent

/-- Segments `AB` and `CD` are congruent iff their lengths are equal. -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

/-- Congruence with explicit segment witnesses `SP1 = [a,b]` and `SP2 = [c,d]`. -/
@[simp]
def congruentSegmentsBy (SP1 SP2 : Segment) (a b c d : Point) : Prop :=
  SP1 = Segment.endpoints a b ∧ SP2 = Segment.endpoints c d ∧ congruentSegments a b c d


-- 5. Two lines being perpendicular (witnessed at a point with side-points)

/-- Lines `L` and `M` are perpendicular, witnessed at point `i` with points `a` on `L`
and `c` on `M`, iff:
- `L` and `M` intersect;
- `a,i,c` form a rectilinear angle with sides on `L` and `M`;
- the angle ∠ AIC is a right angle (∟). -/
@[simp]
def perpendicularAt (L M : Line) (i a c : Point) : Prop :=
  L.intersectsLine M ∧ formRectilinearAngle a i c L M ∧ (∠ a:i:c) = ∟


/-!
Extension: Length ratios, triangle angle sum, triangle similarity, and convex quadrilaterals.

This file introduces:
1. segmentLength and lengthRatio functions (points- and segment-based) and equality of two length ratios.
2. triangleAngleSum: the three interior angles of a triangle sum to ∟ + ∟.
3. trianglesSimilar: canonical definition using all corresponding angles and proportional sides.
4. formConvexQuadrilateral: a convex quadrilateral specified by four vertices and their side lines.

All definitions are quantifier-free and avoid disjunction, in accordance with the DSL constraints.
-/


/-! 0. Segment length and ratio-of-lengths helpers -/

/-- The length of a segment, obtained by destructing its endpoints. -/
@[simp] noncomputable
def segmentLength (SP : Segment) : ℝ :=
  match SP with
  | Segment.endpoints a b => |(a─b)|

/-- The ratio of lengths of two segments `SP1 / SP2`. -/
@[simp] noncomputable
def lengthRatioOfSegments (SP1 SP2 : Segment) : ℝ :=
  segmentLength SP1 / segmentLength SP2

/-- The ratio of lengths of segments `[a,b] / [c,d]` via their endpoints. -/
@[simp] noncomputable
def lengthRatio (a b c d : Point) : ℝ :=
  |(a─b)| / |(c─d)|

/-- The ratio of segment lengths is positive (simple witness-style predicate). -/
@[simp]
def lengthRatioIsPositive (SP1 SP2 : Segment) : Prop :=
  lengthRatioOfSegments SP1 SP2 > 0


/-! 1. Two ratios of lengths of line segments being equal -/

/-- Equality of two ratios of lengths given by endpoints:
(|AB| / |CD|) = (|EF| / |GH|). -/
@[simp]
def equalLengthRatios (a b c d e f g h : Point) : Prop :=
  (|(a─b)| / |(c─d)|) = (|(e─f)| / |(g─h)|)

/-- Equality of two ratios of lengths using segment witnesses. -/
@[simp]
def equalLengthRatiosBySegments (SP1 SP2 SP3 SP4 : Segment) : Prop :=
  lengthRatioOfSegments SP1 SP2 = lengthRatioOfSegments SP3 SP4


/-! 2. The three angles in a triangle summing to 180 degrees (i.e., ∟ + ∟) -/

/-- For a non-degenerate triangle `ABC`, the sum of its interior angles is ∟ + ∟. -/
@[simp]
def triangleAngleSum (a b c : Point) : Prop :=
  pointsDefineTriangle a b c ∧
  (Triangle.angleAtA a b c + Triangle.angleAtB a b c + Triangle.angleAtC a b c = ∟ + ∟)


/-! 3. Two triangles being similar (canonical definition)
- all three corresponding angles are equal,
- all three corresponding side-length ratios are equal (pairwise chain).
We require both triples of points to define non-degenerate triangles.
-/

/-- Triangles `ABC` and `DEF` are similar if:
- both are non-degenerate;
- corresponding angles are equal:
    ∠ BAC = ∠ EDF, ∠ ABC = ∠ DEF, ∠ ACB = ∠ DFE;
- corresponding sides are equally proportional:
    |AB|/|DE| = |BC|/|EF| = |CA|/|FD|.
We encode the side-ratio chain as two equalities:
    |AB|/|DE| = |BC|/|EF|  and  |BC|/|EF| = |CA|/|FD|. -/
@[simp]
def trianglesSimilar (a b c d e f : Point) : Prop :=
  pointsDefineTriangle a b c ∧ pointsDefineTriangle d e f ∧
  -- angle correspondences
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  -- side-ratio correspondences (chained)
  (|(a─b)| / |(d─e)|) = (|(b─c)| / |(e─f)|) ∧
  (|(b─c)| / |(e─f)|) = (|(c─a)| / |(f─d)|)


/-! 4. A convex quadrilateral defined by four non-collinear points -/

/-- Pairwise distinctness for four points. -/
@[simp]
def pairwiseDistinct4Points (a b c d : Point) : Prop :=
  pairwiseDistinct [a, b, c, d]

/-- Pairwise distinctness for four lines. -/
@[simp]
def pairwiseDistinct4Lines (L1 L2 L3 L4 : Line) : Prop :=
  L1 ≠ L2 ∧ L2 ≠ L3 ∧ L3 ≠ L4 ∧ L4 ≠ L1 ∧ L1 ≠ L3 ∧ L2 ≠ L4

/-- Four points `a,b,c,d` with side-lines `AB,BC,CD,DA` form a convex quadrilateral iff:
- consecutive vertices lie on their side lines with distinct endpoints;
- the four vertices are pairwise distinct;
- each consecutive triple is non-collinear (no straight angles);
- side lines are pairwise distinct;
- adjacent sides meet (intersect);
- for each side line, the two nonincident vertices lie on the same side of that line
  (this encodes convexity and non-self-intersection).

The order is strictly respected: `a-b` on `AB`, `b-c` on `BC`, `c-d` on `CD`, `d-a` on `DA`. -/
@[simp]
def formConvexQuadrilateral (a b c d : Point) (AB BC CD DA : Line) : Prop :=
  -- sides with endpoints
  distinctPointsOnLine a b AB ∧
  distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧
  distinctPointsOnLine d a DA ∧
  -- vertex distinctness
  pairwiseDistinct4Points a b c d ∧
  -- non-collinearity (no straight angles at the vertices)
  nonCollinearPoints a b c ∧
  nonCollinearPoints b c d ∧
  nonCollinearPoints c d a ∧
  nonCollinearPoints d a b ∧
  -- line distinctness
  pairwiseDistinct4Lines AB BC CD DA ∧
  -- adjacent sides intersect (consistency with shared vertices)
  AB.intersectsLine BC ∧
  BC.intersectsLine CD ∧
  CD.intersectsLine DA ∧
  DA.intersectsLine AB ∧
  -- convexity via "same side" constraints
  c.sameSide d AB ∧
  d.sameSide a BC ∧
  a.sameSide b CD ∧
  b.sameSide c DA


/-!
New extensions: diagonals of a quadrilateral, general angle-bisecting segment at a vertex,
triangle congruence (canonical), triangles sharing a common side (via side selectors),
and equilateral triangles.

All definitions are quantifier-free, avoid disjunctions, and follow the DSL style.
-/


/-! 1) Diagonals of a quadrilateral

A diagonal is represented by an explicit segment witness whose endpoints are the two
non-adjacent vertices. We provide oriented variants for both diagonals AC and BD
of the ordered quadruple (a, b, c, d). We also require the four vertices to be
pairwise distinct to reflect a proper quadrilateral setup.
-/

/-- `SP` is the diagonal AC of the ordered quadruple (a, b, c, d). -/
@[simp]
def diagonalACOfQuadrilateral (a b c d : Point) (SP : Segment) : Prop :=
  pairwiseDistinct4Points a b c d ∧ SP = Segment.endpoints a c

/-- `SP` is the diagonal BD of the ordered quadruple (a, b, c, d). -/
@[simp]
def diagonalBDOfQuadrilateral (a b c d : Point) (SP : Segment) : Prop :=
  pairwiseDistinct4Points a b c d ∧ SP = Segment.endpoints b d

/-- Oriented variant: `SP` is the diagonal CA (the reverse of AC). -/
@[simp]
def diagonalCAOfQuadrilateral (a b c d : Point) (SP : Segment) : Prop :=
  pairwiseDistinct4Points a b c d ∧ SP = Segment.endpoints c a

/-- Oriented variant: `SP` is the diagonal DB (the reverse of BD). -/
@[simp]
def diagonalDBOfQuadrilateral (a b c d : Point) (SP : Segment) : Prop :=
  pairwiseDistinct4Points a b c d ∧ SP = Segment.endpoints d b



/-! 2) A line segment bisecting an angle at its vertex

General, angle-centric formulation at vertex `b`. The user provides the side
lines `AB` and `BC` of the angle and the line `BP` on which the bisecting segment lies.
Interior of the angle is witnessed using `sameSide`, and the sub-angles are equal.
-/

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



/-! 3) Triangle congruence (canonical definition)

Triangles ABC and DEF are congruent iff both are non-degenerate, all corresponding
angles are equal, and all corresponding sides are equal.
-/

/-- Triangles `ABC` and `DEF` are congruent iff:
- both define non-degenerate triangles;
- corresponding angles are equal:
    ∠ BAC = ∠ EDF, ∠ ABC = ∠ DEF, ∠ ACB = ∠ DFE;
- corresponding sides are equal in length:
    |AB| = |DE|, |BC| = |EF|, |CA| = |FD|. -/
@[simp]
def trianglesCongruent (a b c d e f : Point) : Prop :=
  pointsDefineTriangle a b c ∧ pointsDefineTriangle d e f ∧
  -- angle correspondences
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  -- side correspondences
  (|(a─b)|) = (|(d─e)|) ∧
  (|(b─c)|) = (|(e─f)|) ∧
  (|(c─a)|) = (|(f─d)|)



/-! 4) Two triangles sharing a common side

We avoid disjunction by using explicit side-selection functions. The user specifies
which side of each triangle is intended as the "shared" one, and we require the two
selected sides (segments) to be definitionally equal.
-/

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

/-- Two triangles `ABC` and `DEF` share a common side, witnessed by choosing side-selectors
for each triangle, when the selected side segments are equal. Typical side selectors are
`Triangle.sideAB`, `Triangle.sideBC`, or `Triangle.sideCA`. -/
@[simp]
def trianglesShareSideBy
    (sel₁ : Point → Point → Point → Segment)
    (sel₂ : Point → Point → Point → Segment)
    (a b c d e f : Point) : Prop :=
  sel₁ a b c = sel₂ d e f



/-! 5) Equilateral triangle

A triangle is equilateral iff all three sides have equal length. We also require
non-degeneracy via `pointsDefineTriangle`.
-/

/-- Triangle `ABC` is equilateral iff it is non-degenerate and
`|AB| = |BC| = |CA|` (encoded as two equalities). -/
@[simp]
def equilateralTriangle (a b c : Point) : Prop :=
  pointsDefineTriangle a b c ∧
  |(a─b)| = |(b─c)| ∧
  |(b─c)| = |(c─a)|


/-!
Extension: Isosceles triangles and line cuts on triangle sides with parallelism.

This file introduces:
1. Isosceles triangles, with vertex-specific and selector-based variants.
2. A line intersecting two specified sides of a triangle at given points.
3. The above scenario with the line also parallel to the third side.

All definitions are quantifier-free, avoid disjunction, and follow the DSL style.
-/


/-! 1. Isosceles triangles -/

/-- Triangle `ABC` is isosceles at vertex `A` iff it is non-degenerate and `|AB| = |AC|`. -/
@[simp]
def isoscelesAtA (a b c : Point) : Prop :=
  pointsDefineTriangle a b c ∧ |(a─b)| = |(a─c)|

/-- Triangle `ABC` is isosceles at vertex `B` iff it is non-degenerate and `|BA| = |BC|`. -/
@[simp]
def isoscelesAtB (a b c : Point) : Prop :=
  pointsDefineTriangle a b c ∧ |(b─a)| = |(b─c)|

/-- Triangle `ABC` is isosceles at vertex `C` iff it is non-degenerate and `|CA| = |CB|`. -/
@[simp]
def isoscelesAtC (a b c : Point) : Prop :=
  pointsDefineTriangle a b c ∧ |(c─a)| = |(c─b)|

/-- General selector-based isosceles condition:
`sel₁` and `sel₂` pick two sides of triangle `ABC` as segments; the triangle is isosceles
by these selectors iff the selected sides have equal length.
Typical selectors are `Triangle.sideAB`, `Triangle.sideBC`, or `Triangle.sideCA`. -/
@[simp]
def isoscelesBy
    (sel₁ sel₂ : Point → Point → Point → Segment)
    (a b c : Point) : Prop :=
  pointsDefineTriangle a b c ∧
  segmentLength (sel₁ a b c) = segmentLength (sel₂ a b c)



/-! 2. A line intersecting two sides of a triangle at specified points -/

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



/-! 3. A line intersecting two sides of a triangle and parallel to the third side -/

/-- Line `L` intersects sides `AB` and `AC` of triangle `ABC` at points `p` and `q`,
and is parallel to the third side `BC`. We also include compatibility with the DSL
primitive `intersectsLine` for the two met sides. -/
@[simp]
def lineCutsABandACParallelBC
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine CA ∧ between c q a ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine AB ∧ L.intersectsLine CA ∧
  parallel L BC

/-- Line `L` intersects sides `AB` and `BC` of triangle `ABC` at points `p` and `q`,
and is parallel to the third side `CA`. We also include `intersectsLine` with the met sides. -/
@[simp]
def lineCutsABandBCParallelCA
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine AB ∧ L.intersectsLine BC ∧
  parallel L CA

/-- Line `L` intersects sides `AC` and `BC` of triangle `ABC` at points `p` and `q`,
and is parallel to the third side `AB`. We also include `intersectsLine` with the met sides. -/
@[simp]
def lineCutsACandBCParallelAB
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧ between c p a ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine CA ∧ L.intersectsLine BC ∧
  parallel L AB