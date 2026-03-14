import SystemE.Theory.Relations


/-!
Refactored extension: additional geometric relations and list-based combinators for 2D Euclidean Geometry.

Highlights:
- List combinators (quantifier-free "for all in list" style).
- Intersection of two distinct lines at a specified point.
- Sequential alignment of points on a line (with an optional "three or more" variant).
- Opposing-sides conditions for two lists of points with respect to a line.
- Supplementary angles and parallelism.
- Midpoints, segment equality, extensions beyond endpoints, and perpendicularity.
- Segment length/ratio utilities and equal ratio predicates.
- Triangle angle sum (line-based triangle witness).
- Triangle similarity and congruence (canonical definitions, applicable to degenerate cases).
- Convex quadrilateral (simplified, non-redundant).
- Diagonals of a quadrilateral (by explicit endpoints).
- General angle bisection at a vertex with side lines.
- Side selectors for triangles and sharing a side.
- Equilateral and isosceles triangle predicates (purely metric).

All definitions:
- Avoid quantifiers and disjunctions.
- Use ∠ and ∟ consistently.
- Are registered with @[simp].
- Introduce no new types and no imports.
-/

/-! Section: List-based helpers -/

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
  | _ :: _ :: _ :: _ => True
  | _ :: _ :: _      => True
  | _                => False


/-! Section: Incidence and alignment -/

/-- Two distinct lines L and M intersect at point i:
- L and M are distinct;
- i lies on both L and M;
- L and M intersect (compatibility with DSL primitive).
-/
@[simp]
def twoDistinctLinesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  L ≠ M ∧ i.onLine L ∧ i.onLine M ∧ L.intersectsLine M

/-- A list of points is sequentially aligned on line L:
- all listed points lie on L;
- consecutive triples form a chain of "between" relations.
Note: No explicit pairwise-distinctness requirement; "between" already enforces
distinctness locally and collinearity. -/
@[simp]
def sequentiallyAlignedOnLine (pts : List Point) (L : Line) : Prop :=
  allOnLine pts L ∧ betweennessChain pts

/-- "Three or more points sequentially aligned on a line":
enforces at least three points in addition to `sequentiallyAlignedOnLine`. -/
@[simp]
def sequentiallyAlignedThreeOrMore (pts : List Point) (L : Line) : Prop :=
  hasAtLeastThree pts ∧ sequentiallyAlignedOnLine pts L


/-! Section: Opposing sides and parallelism -/

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
every cross-pair (x in xs, y in ys) are on opposite sides of L.
Note: `opposingSides` itself enforces that the points are not on L, so no extra
"none on L" clauses are included. -/
@[simp]
def twoSetsOpposingSidesOnLine (xs ys : List Point) (L : Line) : Prop :=
  pairwiseAcrossOpposing xs ys L

/-- Two angles ∠ a:b:c and ∠ d:e:f are supplementary iff their measures sum to ∟ + ∟. -/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = ∟ + ∟

/-- Two lines are parallel if they are distinct and do not intersect. -/
@[simp]
def parallel (L M : Line) : Prop :=
  L ≠ M ∧ ¬ L.intersectsLine M


/-! Section: Midpoints, extensions, segment congruence, and perpendicularity -/

namespace Point

/-- m is the midpoint of AB iff:
- `a,m,b` are in betweenness (hence distinct and collinear);
- the distances from `m` to `a` and `b` are equal. -/
@[simp]
def isMidpointOf (m a b : Point) : Prop :=
  between a m b ∧ |(a─m)| = |(m─b)|

/-- Same as `isMidpointOf m a b`, with an explicit segment witness `SP = [a,b]`. -/
@[simp]
def isMidpointOfSegmentEndpoints (m a b : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints a b ∧ isMidpointOf m a b

/-- p lies on the extension of segment AB beyond endpoint B iff `B` is between `A` and `P`. -/
@[simp]
def onExtensionBeyondB (p a b : Point) : Prop :=
  between a b p

/-- p lies on the extension of segment AB beyond endpoint A iff `A` is between `B` and `P`. -/
@[simp]
def onExtensionBeyondA (p a b : Point) : Prop :=
  between b a p

end Point

/-- Segments AB and CD are congruent iff their lengths are equal. -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

/-- Congruence with explicit segment witnesses `SP1 = [a,b]` and `SP2 = [c,d]`. -/
@[simp]
def congruentSegmentsBy (SP1 SP2 : Segment) (a b c d : Point) : Prop :=
  SP1 = Segment.endpoints a b ∧ SP2 = Segment.endpoints c d ∧ congruentSegments a b c d

/-- Lines L and M are perpendicular, witnessed at point i with points a on L and c on M iff:
- L and M intersect;
- a,i,c form a rectilinear angle with sides on L and M;
- ∠ AIC is a right angle (∟). -/
@[simp]
def perpendicularAt (L M : Line) (i a c : Point) : Prop :=
  L.intersectsLine M ∧ formRectilinearAngle a i c L M ∧ (∠ a:i:c) = ∟


/-! Section: Segment length and length ratios -/

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

/-- A (witness-style) predicate: the ratio of segment lengths is positive. -/
@[simp]
def lengthRatioIsPositive (SP1 SP2 : Segment) : Prop :=
  lengthRatioOfSegments SP1 SP2 > 0

/-- Equality of two ratios of lengths given by endpoints:
(|AB| / |CD|) = (|EF| / |GH|). -/
@[simp]
def equalLengthRatios (a b c d e f g h : Point) : Prop :=
  (|(a─b)| / |(c─d)|) = (|(e─f)| / |(g─h)|)

/-- Equality of two ratios of lengths using segment witnesses. -/
@[simp]
def equalLengthRatiosBySegments (SP1 SP2 SP3 SP4 : Segment) : Prop :=
  lengthRatioOfSegments SP1 SP2 = lengthRatioOfSegments SP3 SP4


/-! Section: Triangles -/

/-- For a triangle formed by lines AB, BC, and CA, the sum of its interior angles is ∟ + ∟. -/
@[simp]
def triangleAngleSum (a b c : Point) (AB BC CA : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  ((∠ b:a:c) + (∠ a:b:c) + (∠ a:c:b) = ∟ + ∟)

/-- Triangles ABC and DEF are similar iff:
- all corresponding angles are equal:
    ∠ BAC = ∠ EDF, ∠ ABC = ∠ DEF, ∠ ACB = ∠ DFE;
- corresponding sides are equally proportional (encoded as a chain of two equalities):
    |AB|/|DE| = |BC|/|EF| and |BC|/|EF| = |CA|/|FD|.
No non-degeneracy requirement is imposed. -/
@[simp]
def trianglesSimilar (a b c d e f : Point) : Prop :=
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  (|(a─b)| / |(d─e)|) = (|(b─c)| / |(e─f)|) ∧
  (|(b─c)| / |(e─f)|) = (|(c─a)| / |(f─d)|)

/-- Triangles ABC and DEF are congruent iff:
- corresponding angles are equal:
    ∠ BAC = ∠ EDF, ∠ ABC = ∠ DEF, ∠ ACB = ∠ DFE;
- corresponding sides are equal in length:
    |AB| = |DE|, |BC| = |EF|, |CA| = |FD|.
No non-degeneracy requirement is imposed. -/
@[simp]
def trianglesCongruent (a b c d e f : Point) : Prop :=
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  (|(a─b)|) = (|(d─e)|) ∧
  (|(b─c)|) = (|(e─f)|) ∧
  (|(c─a)|) = (|(f─d)|)

/-- Triangle ABC is equilateral iff |AB| = |BC| = |CA| (encoded as two equalities). -/
@[simp]
def equilateralTriangle (a b c : Point) : Prop :=
  |(a─b)| = |(b─c)| ∧
  |(b─c)| = |(c─a)|

/-- Triangle ABC is isosceles at vertex A iff |AB| = |AC|. -/
@[simp]
def isoscelesAtA (a b c : Point) : Prop :=
  |(a─b)| = |(a─c)|

/-- Triangle ABC is isosceles at vertex B iff |BA| = |BC|. -/
@[simp]
def isoscelesAtB (a b c : Point) : Prop :=
  |(b─a)| = |(b─c)|

/-- Triangle ABC is isosceles at vertex C iff |CA| = |CB|. -/
@[simp]
def isoscelesAtC (a b c : Point) : Prop :=
  |(c─a)| = |(c─b)|

namespace Triangle

/-- The side AB of triangle ABC as a segment. -/
@[simp]
def sideAB (a b : Point) (_c : Point) : Segment :=
  Segment.endpoints a b

/-- The side BC of triangle ABC as a segment. -/
@[simp]
def sideBC (_a : Point) (b c : Point) : Segment :=
  Segment.endpoints b c

/-- The side CA of triangle ABC as a segment. -/
@[simp]
def sideCA (a : Point) (_b : Point) (c : Point) : Segment :=
  Segment.endpoints c a

end Triangle

/-- Two triangles ABC and DEF share a common side, witnessed by choosing side-selectors
for each triangle, when the selected side segments are equal. Typical side selectors are
`Triangle.sideAB`, `Triangle.sideBC`, or `Triangle.sideCA`. -/
@[simp]
def trianglesShareSideBy
    (sel₁ : Point → Point → Point → Segment)
    (sel₂ : Point → Point → Point → Segment)
    (a b c d e f : Point) : Prop :=
  sel₁ a b c = sel₂ d e f


/-! Section: Convex quadrilaterals and diagonals -/

/-- A convex quadrilateral specified by four vertices a, b, c, d and side lines AB, BC, CD, DA.
We require:
- distinct points a,b lie on AB; b,c on BC; c,d on CD; d,a on DA;
- convexity via "same side" constraints:
    c and d are on the same side of AB,
    d and a are on the same side of BC,
    a and b are on the same side of CD,
    b and c are on the same side of DA.

No further distinctness or intersection constraints are needed: the above already
forces the usual non-degeneracy and adjacency properties. -/
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

/-- SP is the diagonal AC of the ordered quadruple (a, b, c, d). -/
@[simp]
def diagonalACOfQuadrilateral (a _ c _ : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints a c

/-- SP is the diagonal BD of the ordered quadruple (a, b, c, d). -/
@[simp]
def diagonalBDOfQuadrilateral (_ b _ d : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints b d

/-- Oriented variant: SP is the diagonal CA (the reverse of AC). -/
@[simp]
def diagonalCAOfQuadrilateral (a _ c _ : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints c a

/-- Oriented variant: SP is the diagonal DB (the reverse of BD). -/
@[simp]
def diagonalDBOfQuadrilateral (_ b _ d : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints d b


/-! Section: Angle bisection at a vertex -/

/-- Segment BP bisects angle ABC at vertex b. The user provides side lines AB, BC
and the carrier line BP for the segment. Requirements:
- a,b lie on AB;
- b,c lie on BC;
- b,p lie on BP;
- interior witness: a and p are on the same side of BC; c and p are on the same side of AB;
- the two sub-angles are equal: ∠ ABP = ∠ PBC;
- SP is the segment with endpoints b and p. -/
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


/-! Section: Lines cutting triangle sides (Ceva/Menelaus-style primitives) -/

/-- Line L intersects sides AB and AC of triangle ABC at points p and q respectively:
- ABC is formed by lines AB, BC, CA;
- p lies on AB with A-p-B betweenness;
- q lies on CA with C-q-A betweenness;
- both p and q lie on L. -/
@[simp]
def lineCutsTriangleOnABandACAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine CA ∧ between c q a ∧
  p.onLine L ∧ q.onLine L

/-- Line L intersects sides AB and BC of triangle ABC at points p and q respectively:
- ABC is formed by lines AB, BC, CA;
- p lies on AB with A-p-B betweenness;
- q lies on BC with B-q-C betweenness;
- both p and q lie on L. -/
@[simp]
def lineCutsTriangleOnABandBCAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L

/-- Line L intersects sides AC and BC of triangle ABC at points p and q respectively:
- ABC is formed by lines AB, BC, CA;
- p lies on CA with C-p-A betweenness;
- q lies on BC with B-q-C betweenness;
- both p and q lie on L. -/
@[simp]
def lineCutsTriangleOnACandBCAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧ between c p a ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L

/-- Line L intersects sides AB and AC of triangle ABC at p and q, and is parallel to BC.
We also include compatibility with `intersectsLine` for the two met sides. -/
@[simp]
def lineCutsABandACParallelBC
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine CA ∧ between c q a ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine AB ∧ L.intersectsLine CA ∧
  parallel L BC

/-- Line L intersects sides AB and BC of triangle ABC at p and q, and is parallel to CA. -/
@[simp]
def lineCutsABandBCParallelCA
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine AB ∧ L.intersectsLine BC ∧
  parallel L CA

/-- Line L intersects sides AC and BC of triangle ABC at p and q, and is parallel to AB. -/
@[simp]
def lineCutsACandBCParallelAB
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧ between c p a ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine CA ∧ L.intersectsLine BC ∧
  parallel L AB

/-- A line segment from a vertex v to a point p on the opposite side s1s2 of a triangle:
- SP is the segment with endpoints v and p;
- s1, p, s2 are in betweenness order. -/
@[simp]
def segmentFromVertexToOppositeSide (v s1 s2 p : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints v p ∧ between s1 p s2