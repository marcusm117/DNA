import SystemE.Theory.Relations


/-
New DSL extensions for 2D Euclidean Geometry concepts from the CDG.

This file adds the following concepts (quantifier-free, no disjunctions):
1) twoDistinctLinesIntersectAtPoint L M i:
   Two distinct lines L and M intersect at the explicit point i.

2) threePointsSequentiallyOnLine a b c L:
   Three mutually distinct points a, b, c lie on line L with the sequential order a–b–c.

3) sequentiallyAlignedOnLine pts L:
   Three or more distinct points given as a finite list `pts` lie on line L
   and are sequentially aligned; i.e., for every consecutive triple p_i, p_{i+1}, p_{i+2}
   we have `between p_i p_{i+1} p_{i+2}`.

   Helper predicates:
   - allNe a pts: a ≠ every element of pts
   - pairwiseDistinctPoints pts: all points in pts are mutually distinct
   - allOnLine pts L: every point in pts lies on L
   - atLeastThreePoints pts: pts has length ≥ 3
   - consecutiveTriplesBetween pts: for each overlapping consecutive triple in pts,
     the middle point is between the other two.

4) pointsOnOppositeSidesOfLine As Bs L:
   Two nonempty finite lists of points As and Bs lie on opposite sides of line L.
   This is encoded by requiring every pair (a ∈ As, b ∈ Bs) satisfies a.opposingSides b L.

   Helper predicates:
   - nonemptyPoints pts: pts is nonempty
   - allOpposingWithPoint a Bs L: a is on the opposite side of L from every b ∈ Bs
   - allOpposingAcross As Bs L: every pair (a ∈ As, b ∈ Bs) is on opposing sides of L

5) supplementaryAngles a b c d e f:
   The angles ∠abc and ∠def are supplementary, i.e., their measures sum to 180 degrees,
   represented canonically as ∟ + ∟.

6) parallelLines L M:
   Lines L and M are parallel, meaning they are distinct and do not intersect.

All new relations are registered with @[simp].
-/

/-! Helpers for lists of points (quantifier-free encodings) -/

@[simp]
def allNe (a : Point) : List Point → Prop
| [] => True
| b :: t => a ≠ b ∧ allNe a t

@[simp]
def pairwiseDistinctPoints : List Point → Prop
| [] => True
| a :: t => allNe a t ∧ pairwiseDistinctPoints t

@[simp]
def allOnLine : List Point → Line → Prop
| [], _ => True
| a :: t, L => a.onLine L ∧ allOnLine t L

@[simp]
def atLeastThreePoints : List Point → Prop
| _ :: _ :: _ :: _ => True
| _ => False

@[simp]
def consecutiveTriplesBetween : List Point → Prop
| a :: b :: c :: t => between a b c ∧ consecutiveTriplesBetween (b :: c :: t)
| _ => True

/-! 1) Two distinct lines intersecting at a given point -/
@[simp]
def twoDistinctLinesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  L ≠ M ∧ L.intersectsLine M ∧ i.onLine L ∧ i.onLine M

/-! 2) Three distinct points sequentially aligned on a line (explicit triple) -/
@[simp]
def threePointsSequentiallyOnLine (a b c : Point) (L : Line) : Prop :=
  between a b c ∧ a.onLine L ∧ b.onLine L ∧ c.onLine L

/-! 3) Three or more distinct points sequentially aligned on a line (finite list form) -/
@[simp]
def sequentiallyAlignedOnLine (pts : List Point) (L : Line) : Prop :=
  atLeastThreePoints pts ∧ pairwiseDistinctPoints pts ∧ allOnLine pts L ∧ consecutiveTriplesBetween pts

/-! 4) Two sets of points lying on opposing sides of a line -/

@[simp]
def nonemptyPoints : List Point → Prop
| [] => False
| _ :: _ => True

@[simp]
def allOpposingWithPoint (a : Point) : List Point → Line → Prop
| [], _ => True
| b :: t, L => a.opposingSides b L ∧ allOpposingWithPoint a t L

@[simp]
def allOpposingAcross : List Point → List Point → Line → Prop
| [], _, _ => True
| a :: As, Bs, L => allOpposingWithPoint a Bs L ∧ allOpposingAcross As Bs L

@[simp]
def pointsOnOppositeSidesOfLine (As Bs : List Point) (L : Line) : Prop :=
  nonemptyPoints As ∧ nonemptyPoints Bs ∧ allOpposingAcross As Bs L

/-! 5) Supplementary angles: sum to 180 degrees represented canonically as ∟ + ∟ -/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = (∟ + ∟)

/-! 6) Parallel lines: distinct and non-intersecting -/
@[simp]
def parallelLines (L M : Line) : Prop :=
  L ≠ M ∧ ¬ (L.intersectsLine M)


/-
New DSL extensions for 2D Euclidean Geometry concepts from the CDG (quantifier-free, no disjunctions).

This file adds the following concepts:

1) congruentAngles a b c d e f:
   The angles ∠abc and ∠def are congruent (their measures are equal).

2) noncollinearPoints a b c:
   Points a, b, c are pairwise distinct and not collinear, expressed canonically
   by forbidding each of the three "between" configurations.

   Helper:
   - distinctPoints3 a b c: a, b, c are pairwise distinct.

3) triangleDefinedByNoncollinearPoints a b c T:
   The triangle T is exactly △ a:b:c and the points a, b, c are noncollinear.

4) trianglesShareCommonVertexAt p a1 b1 a2 b2 T1 T2:
   The triangles T1 and T2 share the explicit common vertex p:
   T1 = △ p:a1:b1 and T2 = △ p:a2:b2. No disjunctions are used; the shared
   vertex is explicitly provided by the user.

5) angleAtA/angleAtB/angleAtC:
   The angle at a chosen vertex of △ a:b:c, returned as a real-valued angle measure:
   - angleAtA a b c = ∠ b:a:c
   - angleAtB a b c = ∠ a:b:c
   - angleAtC a b c = ∠ a:c:b

6) segmentFromVertex{A,B,C}ToOppositeSide a b c p L s:
   A segment from a specified vertex (A, B, or C) of △ a:b:c to an explicit
   interior point p on the opposite side, carried by a given explicit line L.
   We encode “point on the side” via between:
   - segmentFromVertexAToOppositeSide a b c p L s:
       s = segment a–p, p is between b and c, and b, p, c lie on L
   - segmentFromVertexBToOppositeSide a b c p L s:
       s = segment b–p, p is between c and a, and c, p, a lie on L
   - segmentFromVertexCToOppositeSide a b c p L s:
       s = segment c–p, p is between a and b, and a, p, b lie on L

All new relations and functions are registered with @[simp].
-/

/-! 1) Congruent angles (measures equal) -/
@[simp]
def congruentAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) = (∠ d:e:f)

/-! 2) Non-collinearity of a triple of points -/

@[simp]
def distinctPoints3 (a b c : Point) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ a

/-- Points a, b, c are pairwise distinct and not collinear.
    Canonically: none of the three "between" configurations holds. -/
@[simp]
def noncollinearPoints (a b c : Point) : Prop :=
  distinctPoints3 a b c ∧
  ¬ between a b c ∧ ¬ between b c a ∧ ¬ between c a b

/-! 3) A triangle defined by three non-collinear points -/

/-- Triangle T is exactly △ a:b:c and a, b, c are non-collinear. -/
@[simp]
def triangleDefinedByNoncollinearPoints (a b c : Point) (T : Triangle) : Prop :=
  T = Triangle.ofPoints a b c ∧ noncollinearPoints a b c

/-! 4) Two triangles sharing an explicit common vertex -/

/-- Triangles T1 and T2 share the explicit common vertex p:
    T1 = △ p:a1:b1 and T2 = △ p:a2:b2. -/
@[simp]
def trianglesShareCommonVertexAt
  (p a1 b1 a2 b2 : Point) (T1 T2 : Triangle) : Prop :=
  T1 = Triangle.ofPoints p a1 b1 ∧ T2 = Triangle.ofPoints p a2 b2

/-! 5) Angles at vertices of a triangle (as real-valued measures) -/
@[simp]
def angleAtA (a b c : Point) : ℝ := (∠ b:a:c)

@[simp]
def angleAtB (a b c : Point) : ℝ := (∠ a:b:c)

@[simp]
def angleAtC (a b c : Point) : ℝ := (∠ a:c:b)

/-! 6) Segment from a vertex to an interior point on the opposite side -/

/-- From vertex A to interior point p on side BC carried by line L. -/
@[simp]
def segmentFromVertexAToOppositeSide
  (a b c p : Point) (L : Line) (s : Segment) : Prop :=
  s = Segment.endpoints a p ∧ between b p c ∧ b.onLine L ∧ p.onLine L ∧ c.onLine L

/-- From vertex B to interior point p on side CA carried by line L. -/
@[simp]
def segmentFromVertexBToOppositeSide
  (a b c p : Point) (L : Line) (s : Segment) : Prop :=
  s = Segment.endpoints b p ∧ between c p a ∧ c.onLine L ∧ p.onLine L ∧ a.onLine L

/-- From vertex C to interior point p on side AB carried by line L. -/
@[simp]
def segmentFromVertexCToOppositeSide
  (a b c p : Point) (L : Line) (s : Segment) : Prop :=
  s = Segment.endpoints c p ∧ between a p b ∧ a.onLine L ∧ p.onLine L ∧ b.onLine L


/-
New DSL extensions implementing concepts from the CDG (quantifier-free, no disjunctions).

Added concepts:

1) Point.isMidpointOf m a b:
   m is the midpoint of segment AB: m lies between A and B and |AM| = |MB|.

2) Point.onExtensionOfSegmentBeyondA p a b:
   p lies on the extension of segment AB beyond endpoint A, i.e., B–A–P is ordered.

   Point.onExtensionOfSegmentBeyondB p a b:
   p lies on the extension of segment AB beyond endpoint B, i.e., A–B–P is ordered.

3) congruentSegments a b c d:
   Segment AB is congruent to segment CD: |AB| = |CD|.

4) segmentBisectsAngleAtVertex{A,B,C} a b c p T L s:
   A segment s from the specified vertex to point p lies on explicit line L
   and bisects the corresponding vertex angle of triangle T = △ a:b:c:
   - At A: ∠ b:a:p = ∠ p:a:c
   - At B: ∠ a:b:p = ∠ p:b:c
   - At C: ∠ a:c:p = ∠ p:c:b

5) perpendicularLinesAtPoint L M i a c:
   Lines L and M are perpendicular at explicit intersection point i, witnessed by
   points a ∈ L and c ∈ M, with the right angle measure ∟ at i: ∠ a:i:c = ∟.
-/

namespace Point

/-- m is the midpoint of segment AB: m lies between A and B and the two subsegments have equal length. -/
@[simp]
def isMidpointOf (m a b : Point) : Prop :=
  between a m b ∧ |(a─m)| = |(m─b)|

/-- p lies on the extension of segment AB beyond endpoint A, encoded as the order B–A–P. -/
@[simp]
def onExtensionOfSegmentBeyondA (p : Point) (a b : Point) : Prop :=
  between b a p

/-- p lies on the extension of segment AB beyond endpoint B, encoded as the order A–B–P. -/
@[simp]
def onExtensionOfSegmentBeyondB (p : Point) (a b : Point) : Prop :=
  between a b p

end Point

/-- Segment AB is congruent to segment CD (equal lengths). -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

/-- A segment from vertex A to p lies on L, belongs to triangle T = △ a:b:c, and bisects ∠BAC. -/
@[simp]
def segmentBisectsAngleAtVertexA
  (a b c p : Point) (T : Triangle) (L : Line) (s : Segment) : Prop :=
  T = Triangle.ofPoints a b c ∧
  s = Segment.endpoints a p ∧
  a.onLine L ∧ p.onLine L ∧
  (∠ b:a:p) = (∠ p:a:c)

/-- A segment from vertex B to p lies on L, belongs to triangle T = △ a:b:c, and bisects ∠ABC. -/
@[simp]
def segmentBisectsAngleAtVertexB
  (a b c p : Point) (T : Triangle) (L : Line) (s : Segment) : Prop :=
  T = Triangle.ofPoints a b c ∧
  s = Segment.endpoints b p ∧
  b.onLine L ∧ p.onLine L ∧
  (∠ a:b:p) = (∠ p:b:c)

/-- A segment from vertex C to p lies on L, belongs to triangle T = △ a:b:c, and bisects ∠ACB. -/
@[simp]
def segmentBisectsAngleAtVertexC
  (a b c p : Point) (T : Triangle) (L : Line) (s : Segment) : Prop :=
  T = Triangle.ofPoints a b c ∧
  s = Segment.endpoints c p ∧
  c.onLine L ∧ p.onLine L ∧
  (∠ a:c:p) = (∠ p:c:b)

/-- Perpendicular lines L and M at the explicit intersection point i,
    witnessed by points a ∈ L and c ∈ M with right angle ∟ at i. -/
@[simp]
def perpendicularLinesAtPoint (L M : Line) (i a c : Point) : Prop :=
  twoDistinctLinesIntersectAtPoint L M i ∧
  a.onLine L ∧ c.onLine M ∧
  (∠ a:i:c) = ∟


/-
New DSL extensions from the CDG (quantifier-free, no disjunctions).

This file adds the following concepts:

1) equalSegmentLengthRatios a b c d e f g h:
   Two ratios of segment lengths are equal:
   |AB| / |CD| = |EF| / |GH|.

2) segmentLengthRatio s1 s2:
   A function returning the ratio of the lengths of two explicit segments s1 and s2.
   Helper:
   - segmentNondegenerate s: the endpoints of s are distinct.
   - segmentLengthRatioIsPositive s1 s2: both segments are nondegenerate and the ratio is positive.

3) trianglesSimilar a b c d e f:
   The canonical definition of similarity: all three corresponding angles equal and
   all three corresponding sides proportional (encoded via two equalities of ratios):
   AB/DE = BC/EF = CA/FD.

4) triangleAnglesSumToTwoRightAngles a b c T:
   The three angles of triangle T = △ a:b:c sum to 180 degrees, written canonically as ∟ + ∟.

5) formConvexQuadrilateral a b c d AB BC CD DA AC BD:
   A convex quadrilateral with vertices a, b, c, d in order, carried by explicit side
   lines AB, BC, CD, DA and diagonals AC, BD. The endpoints lie on the corresponding lines,
   adjacent side lines are distinct, every triple of adjacent vertices is non-collinear,
   each pair of non-adjacent vertices lies on the same side of each side-line (convexity),
   and the diagonals intersect.

   Helper:
   - distinctPoints4 a b c d: the four vertices are pairwise distinct.

All new relations and functions are registered with @[simp].
-/

/-! 1) Equality of two ratios of segment lengths (point-level version) -/
@[simp]
def equalSegmentLengthRatios
  (a b c d e f g h : Point) : Prop :=
  (|(a─b)|) / (|(c─d)|) = (|(e─f)|) / (|(g─h)|)

/-! 2) Ratio of lengths: a function on two explicit segments, with positivity predicate -/
@[simp] noncomputable
def segmentLengthRatio : Segment → Segment → ℝ
| Segment.endpoints a b, Segment.endpoints c d => (|(a─b)|) / (|(c─d)|)

@[simp]
def segmentNondegenerate : Segment → Prop
| Segment.endpoints a b => a ≠ b

@[simp]
def segmentLengthRatioIsPositive (s1 s2 : Segment) : Prop :=
  segmentNondegenerate s1 ∧ segmentNondegenerate s2 ∧ segmentLengthRatio s1 s2 > 0

/-! 3) Similarity of two triangles: all angles equal and all sides proportionate -/
@[simp]
def trianglesSimilar (a b c d e f : Point) : Prop :=
  -- Corresponding angles equal
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  -- Corresponding side ratios equal (encode AB/DE = BC/EF = CA/FD via two equalities)
  (|(a─b)|) / (|(d─e)|) = (|(b─c)|) / (|(e─f)|) ∧
  (|(a─b)|) / (|(d─e)|) = (|(c─a)|) / (|(f─d)|)

/-! 4) Angle sum of a triangle is 180 degrees (canonically ∟ + ∟) -/
@[simp]
def triangleAnglesSumToTwoRightAngles (a b c : Point) (T : Triangle) : Prop :=
  T = Triangle.ofPoints a b c ∧
  angleAtA a b c + angleAtB a b c + angleAtC a b c = (∟ + ∟)

/-! Helper: four points are pairwise distinct -/
@[simp]
def distinctPoints4 (a b c d : Point) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d

/-! 5) Convex quadrilateral formed by four non-collinear points with explicit side/diagonal lines -/
@[simp]
def formConvexQuadrilateral
  (a b c d : Point)
  (AB BC CD DA AC BD : Line) : Prop :=
  -- Vertices lie on the intended side lines
  a.onLine AB ∧ b.onLine AB ∧
  b.onLine BC ∧ c.onLine BC ∧
  c.onLine CD ∧ d.onLine CD ∧
  d.onLine DA ∧ a.onLine DA ∧
  -- Diagonals carry their endpoints
  a.onLine AC ∧ c.onLine AC ∧
  b.onLine BD ∧ d.onLine BD ∧
  -- Four distinct vertices
  distinctPoints4 a b c d ∧
  -- Adjacent side lines are distinct (no degeneracy)
  AB ≠ BC ∧ BC ≠ CD ∧ CD ≠ DA ∧ DA ≠ AB ∧
  -- No three adjacent vertices are collinear
  noncollinearPoints a b c ∧
  noncollinearPoints b c d ∧
  noncollinearPoints c d a ∧
  noncollinearPoints d a b ∧
  -- Convexity: the two non-adjacent vertices lie on the same side of each side line
  c.sameSide d AB ∧
  a.sameSide d BC ∧
  a.sameSide b CD ∧
  b.sameSide c DA ∧
  -- Diagonals intersect (simple quadrilateral)
  AC.intersectsLine BD ∧ AC ≠ BD


/-
New DSL extensions from the CDG (quantifier-free, no disjunctions).

Added concepts:

1) diagonalACOfQuadrilateral / diagonalBDOfQuadrilateral:
   A diagonal of a quadrilateral specified by its non-adjacent vertices and the
   explicit line carrying that diagonal:
   - diagonalACOfQuadrilateral a b c d AC s: a, c lie on AC and s = segment a–c with a ≠ c.
   - diagonalBDOfQuadrilateral a b c d BD s: b, d lie on BD and s = segment b–d with b ≠ d.

2) segmentBisectsRectilinearAngle a b c p AB BC s:
   A segment s from vertex b to point p bisects the rectilinear angle ABC carried
   by explicit lines AB and BC. We also require p to lie in the interior of the angle,
   encoded via same-side conditions:
   - s = segment b–p
   - formRectilinearAngle a b c AB BC
   - b lies on both AB and BC (vertex on both sides)
   - p is on the same side of BC as a, and on the same side of AB as c
   - ∠ a:b:p = ∠ p:b:c

3) trianglesCongruent a b c d e f:
   Canonical congruence of triangles △ a:b:c and △ d:e:f:
   all corresponding angles equal and all corresponding sides equal.

4) trianglesShareCommonSideAlong p q r s T1 T2 S:
   Two triangles T1 and T2 share the explicit common side S = segment p–q:
   T1 = △ p:r:q and T2 = △ p:s:q, with p ≠ q.

5) equilateralTriangle a b c T:
   Triangle T = △ a:b:c is equilateral: |AB| = |BC| and |BC| = |CA|.
-/

/-! 1) Diagonals of a quadrilateral as explicit segments on explicit lines -/

/-- The AC-diagonal of a quadrilateral with vertices a, b, c, d:
    a and c lie on the line AC and the diagonal segment is s = a–c, with a ≠ c. -/
@[simp]
def diagonalACOfQuadrilateral
  (a _b c _d : Point) (AC : Line) (s : Segment) : Prop :=
  a.onLine AC ∧ c.onLine AC ∧ s = Segment.endpoints a c ∧ a ≠ c

/-- The BD-diagonal of a quadrilateral with vertices a, b, c, d:
    b and d lie on the line BD and the diagonal segment is s = b–d, with b ≠ d. -/
@[simp]
def diagonalBDOfQuadrilateral
  (_a b _c d : Point) (BD : Line) (s : Segment) : Prop :=
  b.onLine BD ∧ d.onLine BD ∧ s = Segment.endpoints b d ∧ b ≠ d


/-! 2) A segment bisecting a rectilinear angle at its vertex -/

/-- A segment s = b–p bisects the rectilinear angle ABC carried by lines AB and BC.
    We also constrain p to lie in the interior of the angle via same-side conditions. -/
@[simp]
def segmentBisectsRectilinearAngle
  (a b c p : Point) (AB BC : Line) (s : Segment) : Prop :=
  formRectilinearAngle a b c AB BC ∧
  b.onLine AB ∧ b.onLine BC ∧
  s = Segment.endpoints b p ∧
  p.sameSide a BC ∧
  p.sameSide c AB ∧
  (∠ a:b:p) = (∠ p:b:c)


/-! 3) Congruence of two triangles: all corresponding angles and sides equal -/

/-- Triangles △ a:b:c and △ d:e:f are congruent: corresponding angles and sides equal. -/
@[simp]
def trianglesCongruent (a b c d e f : Point) : Prop :=
  -- Corresponding angles equal
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  -- Corresponding sides equal
  (|(a─b)|) = (|(d─e)|) ∧
  (|(b─c)|) = (|(e─f)|) ∧
  (|(c─a)|) = (|(f─d)|)


/-! 4) Two triangles sharing an explicit common side -/

/-- Triangles T1 and T2 share the explicit common side S = segment p–q:
    T1 = △ p:r:q and T2 = △ p:s:q, with p ≠ q. -/
@[simp]
def trianglesShareCommonSideAlong
  (p q r s : Point) (T1 T2 : Triangle) (S : Segment) : Prop :=
  S = Segment.endpoints p q ∧
  p ≠ q ∧
  T1 = Triangle.ofPoints p r q ∧
  T2 = Triangle.ofPoints p s q


/-! 5) Equilateral triangle: all three sides equal (attached to an explicit triangle) -/

/-- Triangle T = △ a:b:c is equilateral: |AB| = |BC| and |BC| = |CA|. -/
@[simp]
def equilateralTriangle (a b c : Point) (T : Triangle) : Prop :=
  T = Triangle.ofPoints a b c ∧
  (|(a─b)|) = (|(b─c)|) ∧
  (|(b─c)|) = (|(c─a)|)


/-
New DSL extensions from the CDG (quantifier-free, no disjunctions).

Added concepts:

1) Isosceles triangle at a specified vertex (three canonical variants):
   - isoscelesTriangleAtA a b c T: T = △ a:b:c and |AB| = |AC|
   - isoscelesTriangleAtB a b c T: T = △ a:b:c and |BA| = |BC|
   - isoscelesTriangleAtC a b c T: T = △ a:b:c and |CA| = |CB|

2) A line intersecting two sides of a triangle and parallel to the third side.
   We provide three explicit variants (no disjunctions), each with explicit
   intersection points on the corresponding sides (as interior points via between):
   - lineIntersectsABandACParallelToBC a b c p q AB BC CA L
   - lineIntersectsABandBCParallelToAC a b c p q AB BC CA L
   - lineIntersectsACandBCParallelToAB a b c p q AB BC CA L

3) A line intersecting two sides of a triangle (without the parallel condition),
   again in three explicit variants:
   - lineIntersectsSidesABandACInTriangle a b c p q AB BC CA L
   - lineIntersectsSidesABandBCInTriangle a b c p q AB BC CA L
   - lineIntersectsSidesACandBCInTriangle a b c p q AB BC CA L

All new relations are registered with @[simp].
-/

/-! 1) Isosceles triangle at a specified vertex (attach to explicit triangle T) -/

/-- T = △ a:b:c is isosceles at A: |AB| = |AC|. -/
@[simp]
def isoscelesTriangleAtA (a b c : Point) (T : Triangle) : Prop :=
  T = Triangle.ofPoints a b c ∧ (|(a─b)|) = (|(a─c)|)

/-- T = △ a:b:c is isosceles at B: |BA| = |BC|. -/
@[simp]
def isoscelesTriangleAtB (a b c : Point) (T : Triangle) : Prop :=
  T = Triangle.ofPoints a b c ∧ (|(b─a)|) = (|(b─c)|)

/-- T = △ a:b:c is isosceles at C: |CA| = |CB|. -/
@[simp]
def isoscelesTriangleAtC (a b c : Point) (T : Triangle) : Prop :=
  T = Triangle.ofPoints a b c ∧ (|(c─a)|) = (|(c─b)|)


/-! 2) A line intersecting two sides of a triangle and parallel to the third side -/

/-- L intersects sides AB and AC of △ a:b:c at interior points p and q respectively,
    and L is parallel to the third side BC. -/
@[simp]
def lineIntersectsABandACParallelToBC
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p b ∧ p.onLine AB ∧ p.onLine L ∧
  between a q c ∧ q.onLine CA ∧ q.onLine L ∧
  AB.intersectsLine L ∧ CA.intersectsLine L ∧
  parallelLines L BC

/-- L intersects sides AB and BC of △ a:b:c at interior points p and q respectively,
    and L is parallel to the third side AC. -/
@[simp]
def lineIntersectsABandBCParallelToAC
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p b ∧ p.onLine AB ∧ p.onLine L ∧
  between b q c ∧ q.onLine BC ∧ q.onLine L ∧
  AB.intersectsLine L ∧ BC.intersectsLine L ∧
  parallelLines L CA

/-- L intersects sides AC and BC of △ a:b:c at interior points p and q respectively,
    and L is parallel to the third side AB. -/
@[simp]
def lineIntersectsACandBCParallelToAB
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p c ∧ p.onLine CA ∧ p.onLine L ∧
  between b q c ∧ q.onLine BC ∧ q.onLine L ∧
  CA.intersectsLine L ∧ BC.intersectsLine L ∧
  parallelLines L AB


/-! 3) A line intersecting two sides of a triangle (without the parallel requirement) -/

/-- L intersects sides AB and AC of △ a:b:c at interior points p and q respectively. -/
@[simp]
def lineIntersectsSidesABandACInTriangle
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p b ∧ p.onLine AB ∧ p.onLine L ∧
  between a q c ∧ q.onLine CA ∧ q.onLine L ∧
  AB.intersectsLine L ∧ CA.intersectsLine L

/-- L intersects sides AB and BC of △ a:b:c at interior points p and q respectively. -/
@[simp]
def lineIntersectsSidesABandBCInTriangle
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p b ∧ p.onLine AB ∧ p.onLine L ∧
  between b q c ∧ q.onLine BC ∧ q.onLine L ∧
  AB.intersectsLine L ∧ BC.intersectsLine L

/-- L intersects sides AC and BC of △ a:b:c at interior points p and q respectively. -/
@[simp]
def lineIntersectsSidesACandBCInTriangle
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  between a p c ∧ p.onLine CA ∧ p.onLine L ∧
  between b q c ∧ q.onLine BC ∧ q.onLine L ∧
  CA.intersectsLine L ∧ BC.intersectsLine L