import SystemE.Theory.Relations


/-
New relations and helpers extending the current DSL.
All definitions are quantifier-free and avoid disjunction, following the guidelines.
They are registered under `simp` so they can be unfolded and used by the simplifier.
-/

/-!
Two distinct lines intersecting at a given point.
This captures the canonical situation “L and M meet at i” with the lines required to be distinct.
-/
@[simp]
def twoDistinctLinesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  L ≠ M ∧ i.onLine L ∧ i.onLine M


/-!
Two lines being parallel (distinct and non-intersecting).
Note: Our canonical definition enforces distinctness and the absence of intersection.
-/
@[simp]
def parallelLines (L M : Line) : Prop :=
  L ≠ M ∧ ¬ L.intersectsLine M


/-!
Two angles are supplementary: the sum of their measures is a straight angle.
By convention of the DSL, the straight angle is represented as `∟ + ∟`.
-/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = (∟ + ∟)


/-!
Helpers for handling finite families of points without quantifiers.
We use Lists of points and recursive predicates to express “all on a line”,
“pairwise distinct”, and “consecutive betweens” (sequential alignment).
-/

/-- All points in the list lie on the given line L. -/
@[simp]
def pointsAllOnLine (ps : List Point) (L : Line) : Prop :=
  match ps with
  | []      => True
  | p :: ps => p.onLine L ∧ pointsAllOnLine ps L

/-- a is distinct from every point in the list. -/
@[simp]
def allNeFromHead (a : Point) (ps : List Point) : Prop :=
  match ps with
  | []      => True
  | b :: bs => a ≠ b ∧ allNeFromHead a bs

/-- Points in the list are pairwise distinct. -/
@[simp]
def pointsPairwiseDistinct (ps : List Point) : Prop :=
  match ps with
  | []      => True
  | p :: ps => allNeFromHead p ps ∧ pointsPairwiseDistinct ps

/-- The list has length at least 3 (i.e. contains a triple). -/
@[simp]
def hasLengthAtLeast3 (ps : List Point) : Prop :=
  match ps with
  | _ :: _ :: _ :: _ => True
  | _                => False

/-- Consecutive betweens along a list:
    for p1 p2 p3 p4 ... requires between p1 p2 p3 and between p2 p3 p4, etc. -/
@[simp]
def consecutiveBetweens (ps : List Point) : Prop :=
  match ps with
  | p1 :: p2 :: p3 :: rest => between p1 p2 p3 ∧ consecutiveBetweens (p2 :: p3 :: rest)
  | _                      => True

/-- Three specified points are sequentially aligned on L in the order a-b-c. -/
@[simp]
def threePointsSequentiallyAlignedOnLine (a b c : Point) (L : Line) : Prop :=
  between a b c ∧ a.onLine L ∧ b.onLine L ∧ c.onLine L

/-- A list of three or more distinct points is sequentially aligned on the given line L:
    - at least three points are provided,
    - all points are pairwise distinct,
    - all points lie on L,
    - each consecutive triple satisfies the "between" relation. -/
@[simp]
def sequentiallyAlignedOnLine (ps : List Point) (L : Line) : Prop :=
  hasLengthAtLeast3 ps ∧
  pointsPairwiseDistinct ps ∧
  pointsAllOnLine ps L ∧
  consecutiveBetweens ps


/-!
Two sets of points lying on opposing sides of a given line.
We avoid quantifiers by using a designated representative from each set and
requiring every point in a set to be on the same side as its representative.
-/

/-- Every point of ps lies on the same side of L as the reference point ref. -/
@[simp]
def pointsAllSameSideWithRef (ps : List Point) (ref : Point) (L : Line) : Prop :=
  match ps with
  | []      => True
  | p :: ps => p.sameSide ref L ∧ pointsAllSameSideWithRef ps ref L

/-- Two point-sets S and T lie on opposing sides of L,
    witnessed by representatives s0 ∈ side S and t0 ∈ side T:
    - s0 and t0 are on opposite sides of L,
    - every point of S is on the same side of L as s0,
    - every point of T is on the same side of L as t0. -/
@[simp]
def twoPointSetsOnOppositeSidesOfLine
    (S T : List Point) (s0 t0 : Point) (L : Line) : Prop :=
  s0.opposingSides t0 L ∧
  pointsAllSameSideWithRef S s0 L ∧
  pointsAllSameSideWithRef T t0 L


/-!
New concepts from the CDG, implemented in a quantifier-free manner
and aligned with the existing DSL. All definitions are annotated with `@[simp]`
for convenient unfolding by the simplifier.
-/

/-!
1. Two angles in the Euclidean plane being congruent.
   Canonical definition: equality of their measures.
-/
@[simp]
def congruentAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) = (∠ d:e:f)


/-!
2. A triangle defined by three non-collinear points.
   We enforce:
   - the three points are pairwise distinct,
   - no one of them is between the other two (hence not collinear).
-/

/-- Three points are pairwise distinct and non-collinear. -/
@[simp]
def threeNonCollinearPoints (a b c : Point) : Prop :=
  pointsPairwiseDistinct [a, b, c] ∧
  ¬ between a b c ∧
  ¬ between b c a ∧
  ¬ between c a b

/-- A triangle T is the triangle of points a,b,c, with a,b,c non-collinear. -/
@[simp]
def triangleDefinedByNonCollinearPoints (a b c : Point) (T : Triangle) : Prop :=
  T = Triangle.ofPoints a b c ∧ threeNonCollinearPoints a b c


/-!
3. Two triangles sharing a common vertex in the Euclidean plane.
   To avoid disjunctions and quantifiers, the user must explicitly choose
   one vertex from each triangle; the triangles share a vertex iff these
   chosen vertices are equal.
-/
@[simp]
def trianglesShareSpecificVertices (v₁ v₂ : Point) : Prop :=
  v₁ = v₂


/-!
4. The angle at a vertex of a triangle.
   Canonical alias: for triangle abc, the angle at vertex b is ∠ a:b:c.
-/
@[simp]
def triangleAngleAt (a b c : Point) : ℝ :=
  (∠ a:b:c)


/-!
5. A line segment from a vertex of a triangle to a point on the opposite side.
   We provide three specialized (quantifier- and disjunction-free) relations,
   one for each vertex. Each requires:
   - formTriangle a b c AB BC CA,
   - the chosen point lies on the corresponding opposite side line,
   - the chosen point lies between the other two vertices,
   - the segment is exactly the one with endpoints (vertex, chosen point).
-/

/-- Segment from vertex a to a point p on the opposite side BC of triangle abc. -/
@[simp]
def segmentFromAToOppositeSide
    (a b c : Point) (AB BC CA : Line) (p : Point) (S : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine BC ∧
  between b p c ∧
  S = Segment.endpoints a p

/-- Segment from vertex b to a point p on the opposite side CA of triangle abc. -/
@[simp]
def segmentFromBToOppositeSide
    (a b c : Point) (AB BC CA : Line) (p : Point) (S : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧
  between c p a ∧
  S = Segment.endpoints b p

/-- Segment from vertex c to a point p on the opposite side AB of triangle abc. -/
@[simp]
def segmentFromCToOppositeSide
    (a b c : Point) (AB BC CA : Line) (p : Point) (S : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧
  between a p b ∧
  S = Segment.endpoints c p


/-!
Extension: Midpoints, angle-bisecting segments in triangles, extension points beyond segment endpoints,
congruent segments, and perpendicular lines. All definitions are quantifier- and disjunction-free
and registered under `simp` for convenient rewriting.
-/

/-! 1. Midpoint of a segment -/
namespace Point

/-- m is the midpoint of the segment with endpoints a and b:
    m lies between a and b and the subsegments have equal length. -/
@[simp]
def isMidpointOfPoints (m a b : Point) : Prop :=
  between a m b ∧ |(a─m)| = |(m─b)|

/-- m is the midpoint of the explicit segment S = ab. -/
@[simp]
def isMidpointOfSegment (m : Point) (S : Segment) (a b : Point) : Prop :=
  S = Segment.endpoints a b ∧ isMidpointOfPoints m a b

end Point


/-! 2. A line segment bisecting an angle at a vertex of a triangle -/

/-- Segment from vertex a to p on the opposite side BC bisects ∠ b:a:c. -/
@[simp]
def segmentBisectsTriangleAngleAtA
    (a b c : Point) (AB BC CA : Line) (p : Point) (S : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine BC ∧
  between b p c ∧
  S = Segment.endpoints a p ∧
  (∠ b:a:p) = (∠ p:a:c)

/-- Segment from vertex b to p on the opposite side CA bisects ∠ a:b:c. -/
@[simp]
def segmentBisectsTriangleAngleAtB
    (a b c : Point) (AB BC CA : Line) (p : Point) (S : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧
  between c p a ∧
  S = Segment.endpoints b p ∧
  (∠ a:b:p) = (∠ p:b:c)

/-- Segment from vertex c to p on the opposite side AB bisects ∠ b:c:a. -/
@[simp]
def segmentBisectsTriangleAngleAtC
    (a b c : Point) (AB BC CA : Line) (p : Point) (S : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧
  between a p b ∧
  S = Segment.endpoints c p ∧
  (∠ b:c:p) = (∠ p:c:a)


/-! 3. A point lying on the extension of a line segment beyond a specified endpoint -/
namespace Point

/-- p lies on the extension of segment ab beyond endpoint a (i.e., p–a–b). -/
@[simp]
def onExtensionBeyondEndpointA (p a b : Point) : Prop :=
  between p a b

/-- p lies on the extension of segment ab beyond endpoint b (i.e., a–b–p). -/
@[simp]
def onExtensionBeyondEndpointB (p a b : Point) : Prop :=
  between a b p

end Point


/-! 4. Two line segments being congruent (equal lengths) -/

/-- Segments ab and cd are congruent: they have equal lengths. -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

/-- Congruence of two explicit segment objects S₁ = ab and S₂ = cd. -/
@[simp]
def congruentSegmentsAs (S₁ S₂ : Segment) (a b c d : Point) : Prop :=
  S₁ = Segment.endpoints a b ∧
  S₂ = Segment.endpoints c d ∧
  congruentSegments a b c d


/-! 5. Two lines being perpendicular -/

/-- Lines L and M are perpendicular at point i, witnessed by points l ∈ L and m ∈ M
    such that the rectilinear angle l–i–m measures a right angle. The lines are also
    required to be distinct and to intersect at i. -/
@[simp]
def perpendicularLinesAtPoint (L M : Line) (i l m : Point) : Prop :=
  twoDistinctLinesIntersectAtPoint L M i ∧
  formRectilinearAngle l i m L M ∧
  (∠ l:i:m) = ∟


/-!
CDG Implementations: ratios of lengths, triangle angle sum, length-ratio function,
triangle similarity, and convex quadrilateral (defined by four non-collinear points).

All definitions avoid quantifiers and disjunctions and are aligned with the DSL’s
conventions. The straight angle is represented as `∟ + ∟`, never as the numeral 180.
-/

/-! 1. Two ratios of lengths of line segments being equal -/
/-- The ratios |ab|/|cd| and |ef|/|gh| are equal. -/
@[simp] noncomputable
def equalLengthRatios (a b c d e f g h : Point) : Prop :=
  (|(a─b)| / |(c─d)|) = (|(e─f)| / |(g─h)|)


/-! 2. The ratio of lengths function mapping two line segments to a positive real number -/
/-- Length ratio as a function of endpoints: |ab|/|cd|. -/
@[simp] noncomputable
def lengthRatio (a b c d : Point) : ℝ :=
  |(a─b)| / |(c─d)|

/-- The length ratio |ab|/|cd| is positive. -/
@[simp] noncomputable
def lengthRatioPositive (a b c d : Point) : Prop :=
  0 < lengthRatio a b c d

/-- Using explicit segment objects: S₁ = ab and S₂ = cd, the length ratio |ab|/|cd| is positive. -/
@[simp] noncomputable
def lengthRatioForSegments (S₁ S₂ : Segment) (a b c d : Point) : Prop :=
  S₁ = Segment.endpoints a b ∧
  S₂ = Segment.endpoints c d ∧
  lengthRatioPositive a b c d

/-- Length ratio as a function of segments: if S₁ = ab and S₂ = cd, returns |ab|/|cd|.
    Implemented by pattern-matching on the segment constructors. -/
@[simp] noncomputable
def lengthRatioOfSegments (S₁ S₂ : Segment) : ℝ :=
  match S₁, S₂ with
  | Segment.endpoints a b, Segment.endpoints c d => |(a─b)| / |(c─d)|

/-- The segment-based length ratio is positive. -/
@[simp] noncomputable
def lengthRatioOfSegmentsPositive (S₁ S₂ : Segment) : Prop :=
  0 < lengthRatioOfSegments S₁ S₂


/-! 3. Three angles in a triangle sum to a straight angle (∟ + ∟). -/
/-- For triangle abc formed on lines AB, BC, CA, the three interior angles sum to ∟ + ∟. -/
@[simp] noncomputable
def triangleAnglesSumToStraight (a b c : Point) (AB BC CA : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  (∠ b:a:c) + (∠ c:b:a) + (∠ a:c:b) = (∟ + ∟)


/-! 4. Two triangles being similar (canonical definition).
    We require:
    - each point-triple defines a non-degenerate triangle,
    - all three corresponding angles are equal,
    - all three corresponding side ratios are equal (via chained equalities).
-/
/-- Triangles abc and def are similar: all three corresponding angles are equal and
    all three corresponding side ratios are equal. -/
@[simp] noncomputable
def trianglesSimilar (a b c d e f : Point) : Prop :=
  threeNonCollinearPoints a b c ∧
  threeNonCollinearPoints d e f ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ b:c:a) = (∠ e:f:d) ∧
  (∠ c:a:b) = (∠ f:d:e) ∧
  (|(a─b)| / |(d─e)|) = (|(b─c)| / |(e─f)|) ∧
  (|(b─c)| / |(e─f)|) = (|(c─a)| / |(f─d)|)

/-- Variant with explicit triangle objects. -/
@[simp] noncomputable
def trianglesSimilarAs
    (T₁ T₂ : Triangle) (a b c d e f : Point) : Prop :=
  T₁ = Triangle.ofPoints a b c ∧
  T₂ = Triangle.ofPoints d e f ∧
  trianglesSimilar a b c d e f


/-! 5. A convex quadrilateral defined by four non-collinear points.
    We use only the four vertices and the four side lines (no diagonals),
    following the DSL guideline to avoid auxiliary elements like diagonals.

    Conditions:
    - the four vertices are pairwise distinct,
    - consecutive vertex pairs lie on their designated side lines,
    - all side lines are distinct,
    - each consecutive triple of vertices is non-collinear,
    - convexity is captured via same-side conditions:
      c and d lie on the same side of AB,
      d and a lie on the same side of BC,
      a and b lie on the same side of CD,
      b and c lie on the same side of DA.
-/
/-- Points a, b, c, d with side lines AB, BC, CD, DA form a convex quadrilateral. -/
@[simp]
def formConvexQuadrilateral
    (a b c d : Point) (AB BC CD DA : Line) : Prop :=
  pointsPairwiseDistinct [a, b, c, d] ∧
  distinctPointsOnLine a b AB ∧
  distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧
  distinctPointsOnLine d a DA ∧
  AB ≠ BC ∧ BC ≠ CD ∧ CD ≠ DA ∧ DA ≠ AB ∧
  AB ≠ CD ∧ BC ≠ DA ∧
  threeNonCollinearPoints a b c ∧
  threeNonCollinearPoints b c d ∧
  threeNonCollinearPoints c d a ∧
  threeNonCollinearPoints d a b ∧
  c.sameSide d AB ∧
  d.sameSide a BC ∧
  a.sameSide b CD ∧
  b.sameSide c DA


/-!
CDG Additions:
- Diagonals of quadrilaterals (as segments joining non-adjacent vertices),
- A general angle-bisecting segment at a vertex of a rectilinear angle,
- Triangle congruence (canonical definition: all corresponding angles equal and all corresponding sides equal),
- Two triangles sharing a common side (quantifier- and disjunction-free, via explicit side choices),
- Equilateral triangles.

All definitions are quantifier-free and avoid disjunctions, as required. They are annotated with `@[simp]`
to register them for the simplifier.
-/

/-! 1. Diagonals of a quadrilateral -/

/-- The segment S is the diagonal AC of the four vertices a, b, c, d (assumed cyclically ordered).
    Non-adjacent here means A and C are opposite vertices. -/
@[simp]
def diagonalACOfQuadrilateral (a b c d : Point) (S : Segment) : Prop :=
  pointsPairwiseDistinct [a, b, c, d] ∧
  S = Segment.endpoints a c

/-- The segment S is the diagonal BD of the four vertices a, b, c, d (assumed cyclically ordered).
    Non-adjacent here means B and D are opposite vertices. -/
@[simp]
def diagonalBDOfQuadrilateral (a b c d : Point) (S : Segment) : Prop :=
  pointsPairwiseDistinct [a, b, c, d] ∧
  S = Segment.endpoints b d

/-- Specialization: S is the diagonal AC of the convex quadrilateral abcd with side lines AB, BC, CD, DA. -/
@[simp]
def diagonalACOfConvexQuadrilateral
    (a b c d : Point) (AB BC CD DA : Line) (S : Segment) : Prop :=
  formConvexQuadrilateral a b c d AB BC CD DA ∧
  S = Segment.endpoints a c

/-- Specialization: S is the diagonal BD of the convex quadrilateral abcd with side lines AB, BC, CD, DA. -/
@[simp]
def diagonalBDOfConvexQuadrilateral
    (a b c d : Point) (AB BC CD DA : Line) (S : Segment) : Prop :=
  formConvexQuadrilateral a b c d AB BC CD DA ∧
  S = Segment.endpoints b d


/-! 2. A line segment bisecting an angle at its vertex -/

/-- The segment S = b–p bisects the rectilinear angle a–b–c, witnessed by lines AB and BC.
    Conditions:
    - a,b,c form a rectilinear angle with sides AB and BC,
    - p lies in the interior wedge, encoded via same-side constraints:
      p is on the same side of line BC as a, and on the same side of line AB as c,
    - the two sub-angles are equal: ∠ a:b:p = ∠ p:b:c.
-/
@[simp]
def segmentBisectsAngleAtVertex
    (a b c p : Point) (AB BC : Line) (S : Segment) : Prop :=
  formRectilinearAngle a b c AB BC ∧
  p.sameSide a BC ∧
  p.sameSide c AB ∧
  S = Segment.endpoints b p ∧
  (∠ a:b:p) = (∠ p:b:c)


/-! 3. Two triangles being congruent (canonical definition) -/

/-- Triangles abc and def are congruent iff:
    - both triples are non-collinear,
    - all corresponding angles are equal,
    - and all corresponding sides are equal in length. -/
@[simp]
def trianglesCongruent (a b c d e f : Point) : Prop :=
  threeNonCollinearPoints a b c ∧
  threeNonCollinearPoints d e f ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ b:c:a) = (∠ e:f:d) ∧
  (∠ c:a:b) = (∠ f:d:e) ∧
  |(a─b)| = |(d─e)| ∧
  |(b─c)| = |(e─f)| ∧
  |(c─a)| = |(f─d)|

/-- Variant with explicit triangle objects. -/
@[simp]
def trianglesCongruentAs
    (T₁ T₂ : Triangle) (a b c d e f : Point) : Prop :=
  T₁ = Triangle.ofPoints a b c ∧
  T₂ = Triangle.ofPoints d e f ∧
  trianglesCongruent a b c d e f


/-! 4. Two triangles sharing a common side (quantifier- and disjunction-free) -/
/-!
To avoid disjunctions and unused-variable warnings, we provide explicit side-pair relations.
All point arguments are used; extra conjuncts are tautological equalities that simply
witness the involvement of all triangle vertices without changing logical content.
-/

/-- Triangles abc and def share side AB = DE (with this orientation). -/
@[simp]
def trianglesShareCommonSideAB_DE (a b c d e f : Point) : Prop :=
  Segment.endpoints b c = Segment.endpoints b c ∧
  Segment.endpoints e f = Segment.endpoints e f ∧
  Segment.endpoints a b = Segment.endpoints d e

/-- Triangles abc and def share side BC = EF (with this orientation). -/
@[simp]
def trianglesShareCommonSideBC_EF (a b c d e f : Point) : Prop :=
  Segment.endpoints a b = Segment.endpoints a b ∧
  Segment.endpoints d e = Segment.endpoints d e ∧
  Segment.endpoints b c = Segment.endpoints e f

/-- Triangles abc and def share side CA = FD (with this orientation). -/
@[simp]
def trianglesShareCommonSideCA_FD (a b c d e f : Point) : Prop :=
  Segment.endpoints a b = Segment.endpoints a b ∧
  Segment.endpoints e f = Segment.endpoints e f ∧
  Segment.endpoints c a = Segment.endpoints f d

/-- Segment-based variant: the shared side AB of triangle abc equals the shared side DE of triangle def. -/
@[simp]
def trianglesShareCommonSideAB_DE_viaSegment
    (a b c d e f : Point) (S : Segment) : Prop :=
  Segment.endpoints b c = Segment.endpoints b c ∧
  Segment.endpoints e f = Segment.endpoints e f ∧
  S = Segment.endpoints a b ∧
  S = Segment.endpoints d e

/-- Segment-based variant: the shared side BC of triangle abc equals the shared side EF of triangle def. -/
@[simp]
def trianglesShareCommonSideBC_EF_viaSegment
    (a b c d e f : Point) (S : Segment) : Prop :=
  Segment.endpoints a b = Segment.endpoints a b ∧
  Segment.endpoints d e = Segment.endpoints d e ∧
  S = Segment.endpoints b c ∧
  S = Segment.endpoints e f

/-- Segment-based variant: the shared side CA of triangle abc equals the shared side FD of triangle def. -/
@[simp]
def trianglesShareCommonSideCA_FD_viaSegment
    (a b c d e f : Point) (S : Segment) : Prop :=
  Segment.endpoints a b = Segment.endpoints a b ∧
  Segment.endpoints e f = Segment.endpoints e f ∧
  S = Segment.endpoints c a ∧
  S = Segment.endpoints f d

/-- With explicit triangles: AB of T₁ equals DE of T₂. -/
@[simp]
def trianglesShareCommonSideAB_DE_As
    (T₁ T₂ : Triangle) (a b c d e f : Point) (S : Segment) : Prop :=
  T₁ = Triangle.ofPoints a b c ∧
  T₂ = Triangle.ofPoints d e f ∧
  S = Segment.endpoints a b ∧
  S = Segment.endpoints d e

/-- With explicit triangles: BC of T₁ equals EF of T₂. -/
@[simp]
def trianglesShareCommonSideBC_EF_As
    (T₁ T₂ : Triangle) (a b c d e f : Point) (S : Segment) : Prop :=
  T₁ = Triangle.ofPoints a b c ∧
  T₂ = Triangle.ofPoints d e f ∧
  S = Segment.endpoints b c ∧
  S = Segment.endpoints e f

/-- With explicit triangles: CA of T₁ equals FD of T₂. -/
@[simp]
def trianglesShareCommonSideCA_FD_As
    (T₁ T₂ : Triangle) (a b c d e f : Point) (S : Segment) : Prop :=
  T₁ = Triangle.ofPoints a b c ∧
  T₂ = Triangle.ofPoints d e f ∧
  S = Segment.endpoints c a ∧
  S = Segment.endpoints f d


/-! 5. Equilateral triangles -/

/-- Triangle abc is equilateral: all three side lengths are equal (non-degenerate). -/
@[simp]
def triangleEquilateral (a b c : Point) : Prop :=
  threeNonCollinearPoints a b c ∧
  |(a─b)| = |(b─c)| ∧
  |(b─c)| = |(c─a)|

/-- Variant with an explicit triangle object. -/
@[simp]
def triangleEquilateralAs (T : Triangle) (a b c : Point) : Prop :=
  T = Triangle.ofPoints a b c ∧
  triangleEquilateral a b c


/-!
Additional CDG implementations:
- Isosceles triangles (vertex-specific),
- A line intersecting two sides of a triangle and parallel to the third side,
- A line intersecting two sides of a triangle (with explicit interior intersection points).

All definitions are quantifier-free, avoid disjunctions, and are annotated with `@[simp]`
for convenient use with the simplifier.
-/

/-! 1) Isosceles triangles (vertex-specific) -/

/-- Triangle abc is isosceles at vertex a: the two sides through a are equal. -/
@[simp]
def triangleIsoscelesAtA (a b c : Point) : Prop :=
  threeNonCollinearPoints a b c ∧
  |(a─b)| = |(a─c)|

/-- Triangle abc is isosceles at vertex b: the two sides through b are equal. -/
@[simp]
def triangleIsoscelesAtB (a b c : Point) : Prop :=
  threeNonCollinearPoints a b c ∧
  |(b─c)| = |(b─a)|

/-- Triangle abc is isosceles at vertex c: the two sides through c are equal. -/
@[simp]
def triangleIsoscelesAtC (a b c : Point) : Prop :=
  threeNonCollinearPoints a b c ∧
  |(c─a)| = |(c─b)|

/-- Variant with an explicit triangle object: isosceles at vertex a. -/
@[simp]
def triangleIsoscelesAtAAs (T : Triangle) (a b c : Point) : Prop :=
  T = Triangle.ofPoints a b c ∧
  triangleIsoscelesAtA a b c

/-- Variant with an explicit triangle object: isosceles at vertex b. -/
@[simp]
def triangleIsoscelesAtBAs (T : Triangle) (a b c : Point) : Prop :=
  T = Triangle.ofPoints a b c ∧
  triangleIsoscelesAtB a b c

/-- Variant with an explicit triangle object: isosceles at vertex c. -/
@[simp]
def triangleIsoscelesAtCAs (T : Triangle) (a b c : Point) : Prop :=
  T = Triangle.ofPoints a b c ∧
  triangleIsoscelesAtC a b c


/-! 2) A line intersecting two sides of a triangle and parallel to the third side -/
/-!
We provide three oriented, disjunction-free variants.
Each requires:
- formTriangle a b c AB BC CA,
- interior intersection points (via `between`) on the two corresponding sides,
- those points lie on the given line L,
- L is parallel to the remaining side line (via `parallelLines`).
-/

/-- L is parallel to AB and intersects the other two sides CA and BC at interior points pCA and pBC. -/
@[simp]
def lineParallelToABIntersectingCAandBCInside
    (a b c : Point) (AB BC CA : Line) (L : Line)
    (pCA pBC : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  pCA.onLine CA ∧ between c pCA a ∧ pCA.onLine L ∧
  pBC.onLine BC ∧ between b pBC c ∧ pBC.onLine L ∧
  parallelLines L AB

/-- L is parallel to BC and intersects the other two sides AB and CA at interior points pAB and pCA. -/
@[simp]
def lineParallelToBCIntersectingABandCAInside
    (a b c : Point) (AB BC CA : Line) (L : Line)
    (pAB pCA : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  pAB.onLine AB ∧ between a pAB b ∧ pAB.onLine L ∧
  pCA.onLine CA ∧ between c pCA a ∧ pCA.onLine L ∧
  parallelLines L BC

/-- L is parallel to CA and intersects the other two sides AB and BC at interior points pAB and pBC. -/
@[simp]
def lineParallelToCAIntersectingABandBCInside
    (a b c : Point) (AB BC CA : Line) (L : Line)
    (pAB pBC : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  pAB.onLine AB ∧ between a pAB b ∧ pAB.onLine L ∧
  pBC.onLine BC ∧ between b pBC c ∧ pBC.onLine L ∧
  parallelLines L CA


/-! 3) A line intersecting two sides of a triangle (interior intersections specified) -/
/-!
We provide three oriented variants, each specifying which two sides are met,
together with explicit interior intersection points on those sides.
-/

/-- L intersects sides AB and AC at interior points pAB and pAC. -/
@[simp]
def lineIntersectsABandACInside
    (a b c : Point) (AB BC CA : Line) (L : Line)
    (pAB pAC : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  pAB.onLine AB ∧ between a pAB b ∧ pAB.onLine L ∧
  pAC.onLine CA ∧ between c pAC a ∧ pAC.onLine L

/-- L intersects sides AB and BC at interior points pAB and pBC. -/
@[simp]
def lineIntersectsABandBCInside
    (a b c : Point) (AB BC CA : Line) (L : Line)
    (pAB pBC : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  pAB.onLine AB ∧ between a pAB b ∧ pAB.onLine L ∧
  pBC.onLine BC ∧ between b pBC c ∧ pBC.onLine L

/-- L intersects sides AC and BC at interior points pAC and pBC. -/
@[simp]
def lineIntersectsACandBCInside
    (a b c : Point) (AB BC CA : Line) (L : Line)
    (pAC pBC : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  pAC.onLine CA ∧ between c pAC a ∧ pAC.onLine L ∧
  pBC.onLine BC ∧ between b pBC c ∧ pBC.onLine L