import SystemE.Theory.Relations


/-
Extension: Additional high-level geometric relations without quantifiers or disjunctions.

This file defines the following concepts from the CDG:

1) twoLinesIntersectAtPoint L M i
   - Two distinct lines L and M intersect at the explicitly given point i.

2) sequentiallyAlignedOnLine pts L
   - A list of points (length ≥ 3 recommended) is sequentially aligned on line L.
   - Implemented recursively using the 'between' relation on every consecutive triple,
     ensuring all points lie on L and are globally pairwise distinct.

   Convenience alias:
   - threeOrMoreSequentiallyAlignedOnLine a b c rest L
     is sequentiallyAlignedOnLine (a :: b :: c :: rest) L.

3) setsOnOppositeSidesOfLine S T L
   - Every point of S is on the opposite side of line L from every point of T.

4) supplementaryAngles a b c d e f
   - The angle ∠ a:b:c and the angle ∠ d:e:f are supplementary, i.e. their measures add up to ∟ + ∟.

5) parallelLines L M
   - Lines L and M are parallel in the strict sense: they are distinct and do not intersect.
-/

-- Helper: "head-not-in-tail" predicate for points in a list (no quantifiers).
@[simp] def notMemberPoint (x : Point) : List Point → Prop
  | []       => True
  | y :: ys  => (x ≠ y) ∧ notMemberPoint x ys

-- Helper: global pairwise distinctness of a list of points (no quantifiers).
@[simp] def allDistinctPoints : List Point → Prop
  | []       => True
  | x :: xs  => notMemberPoint x xs ∧ allDistinctPoints xs

-- Helper: all points of a list lie on a given line (no quantifiers).
@[simp] def allPointsOnLine (pts : List Point) (L : Line) : Prop :=
  match pts with
  | []      => True
  | p :: ps => p.onLine L ∧ allPointsOnLine ps L

-- Core: Three points sequentially aligned on a line (uses 'between' and 'onLine').
@[simp] def threePointsSequentiallyAlignedOnLine (a b c : Point) (L : Line) : Prop :=
  between a b c ∧ a.onLine L ∧ b.onLine L ∧ c.onLine L

/-
Sequential alignment on a line for an arbitrary finite sequence of points.

Definition:
- For exactly two points: they are distinct and both on L.
- For exactly three points: 'between' on the triple and all on L.
- For n ≥ 4: enforce 'between' on the first triple (a,b,c), put a,b,c on L,
  ensure 'a' is distinct from all later points (b,c,d,rest),
  and recurse on (b,c,d,rest).

This enforces:
- All points lie on L.
- Every consecutive triple is ordered by 'between'.
- Global pairwise distinctness across the entire list (by recursive notMemberPoint checks).
-/
@[simp] def sequentiallyAlignedOnLine : List Point → Line → Prop
  | [], _ => False
  | [_], _ => False
  | [a, b], L => distinctPointsOnLine a b L
  | [a, b, c], L => threePointsSequentiallyAlignedOnLine a b c L
  | a :: b :: c :: d :: rest, L =>
      threePointsSequentiallyAlignedOnLine a b c L ∧
      notMemberPoint a (b :: c :: d :: rest) ∧
      sequentiallyAlignedOnLine (b :: c :: d :: rest) L

-- Convenience alias for the "three or more" phrasing.
@[simp] def threeOrMoreSequentiallyAlignedOnLine
  (a b c : Point) (rest : List Point) (L : Line) : Prop :=
  sequentiallyAlignedOnLine (a :: b :: c :: rest) L

/-
Two distinct lines intersecting at the explicitly given point i.
We also include L.intersectsLine M to tie into the base DSL's intersection relation.
-/
@[simp] def twoLinesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  (L ≠ M) ∧ i.onLine L ∧ i.onLine M ∧ L.intersectsLine M

/-
Pairwise "opposite sides" across two finite sets (lists) of points.

Every point of S is on the opposite side of line L from every point of T.
This uses only recursion (no quantifiers).
-/
@[simp] def opposingToAllIn (a : Point) (T : List Point) (L : Line) : Prop :=
  match T with
  | []      => True
  | b :: bs => a.opposingSides b L ∧ opposingToAllIn a bs L

@[simp] def setsOnOppositeSidesOfLine (S T : List Point) (L : Line) : Prop :=
  match S with
  | []      => True
  | s :: ss => opposingToAllIn s T L ∧ setsOnOppositeSidesOfLine ss T L

/-
Two angles (given by six points) are supplementary iff their measures add to a straight angle.
Per the DSL specification, we represent a straight angle as ∟ + ∟ (not 180).
-/
@[simp] def supplementaryAngles
  (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = (∟ + ∟)

/-
Two lines are (strictly) parallel iff they are distinct and do not intersect.
-/
@[simp] def parallelLines (L M : Line) : Prop :=
  (L ≠ M) ∧ ¬ L.intersectsLine M


/-
Extension: Congruent angles, non-collinear triples defining triangles, triangles
sharing a vertex (index-based, no disjunction), angles at triangle vertices,
and segments from a triangle vertex to the opposite side.

Conventions:
- No quantifiers (∀/∃) and no disjunctions (∨) are used.
- When "choice among vertices" is needed, we use an explicit numeric index i ∈ {0,1,2}
  to indicate the vertex A/B/C of △ a:b:c, respectively. This avoids any disjunctions.
- For "opposite side" witnessing, we require explicit side-encoding lines AB, BC, CA
  and formTriangle a b c AB BC CA to tie everything to the intended triangle.
-/

/- 1) Congruent angles: equality of their measures. -/
@[simp] def anglesCongruent (a b c d e f : Point) : Prop :=
  (∠ a:b:c) = (∠ d:e:f)


/- 2) Three points being non-collinear and forming a triangle (no disjunctions).

We encode "non-collinear" by forbidding all three possible "between" orderings
and enforcing pairwise distinctness. For three distinct collinear points,
exactly one 'between' relation holds in Euclidean geometry, so the conjunction
of negations yields non-collinearity.
-/
@[simp] def threePointsNonCollinear (a b c : Point) : Prop :=
  (a ≠ b) ∧ (b ≠ c) ∧ (c ≠ a) ∧
  ¬ between a b c ∧ ¬ between b c a ∧ ¬ between c a b

/-
Given a proof that a, b, c are non-collinear (as above), we can form
the triangle object △ a:b:c explicitly. The proof is referenced (to avoid
unused-variable warnings) but not otherwise used computationally.
-/
@[simp] def triangleFromNonCollinearPoints (a b c : Point)
  (h : threePointsNonCollinear a b c) : Triangle :=
  let _ := h
  Triangle.ofPoints a b c

/-
Alternative, line-witnessed version: three non-collinear points forming a triangle,
witnessed by the three distinct sides AB, BC, CA. This is exactly the base DSL's
formTriangle relation, named to reflect the concept "triangle defined by three
non-collinear points".
-/
@[simp] def triangleDefinedByThreeNonCollinearPoints
  (a b c : Point) (AB BC CA : Line) : Prop :=
  formTriangle a b c AB BC CA


/-
3) Two triangles sharing a common vertex.

We avoid disjunctions by using explicit vertex indices i, j ∈ {0,1,2}.
Index mapping:
- 0 ↦ first vertex
- 1 ↦ second vertex
- 2 ↦ third vertex

Definition:
  trianglesShareVertexByIndex T₁ T₂ i j
holds iff the i-th vertex of T₁ equals the j-th vertex of T₂.

Out-of-range indices map to False (no disjunctions, no quantifiers).
-/
@[simp] def trianglesShareVertexByIndex (T₁ T₂ : Triangle) (i j : Nat) : Prop :=
  match T₁, T₂ with
  | Triangle.ofPoints a b c, Triangle.ofPoints d e f =>
    match i, j with
    | 0, 0 => a = d
    | 0, 1 => a = e
    | 0, 2 => a = f
    | 1, 0 => b = d
    | 1, 1 => b = e
    | 1, 2 => b = f
    | 2, 0 => c = d
    | 2, 1 => c = e
    | 2, 2 => c = f
    | _, _ => False


/-
4) Angle at a vertex of a triangle.

We provide:
- Triangle.angleAtVertex T i : ℝ for the angle measure at vertex i.
- Triangle.angleObjAtVertex T i : Angle as an object-level angle at vertex i.

Index mapping (for T = △ a:b:c):
- i = 0: angle at vertex a is ∠ b:a:c
- i = 1: angle at vertex b is ∠ a:b:c
- i = 2: angle at vertex c is ∠ a:c:b
Out-of-range indices default to the angle at vertex b (∠ a:b:c).
-/
namespace Triangle

@[simp] def angleAtVertex (T : Triangle) (i : Nat) : ℝ :=
  match T with
  | Triangle.ofPoints a b c =>
    match i with
    | 0 => (∠ b:a:c)
    | 1 => (∠ a:b:c)
    | 2 => (∠ a:c:b)
    | _ => (∠ a:b:c)

@[simp] def angleObjAtVertex (T : Triangle) (i : Nat) : Angle :=
  match T with
  | Triangle.ofPoints a b c =>
    match i with
    | 0 => Angle.ofPoints b a c
    | 1 => Angle.ofPoints a b c
    | 2 => Angle.ofPoints a c b
    | _ => Angle.ofPoints a b c

end Triangle


/-
5) A line segment from a vertex of a triangle to a point on the opposite side.

We use explicit side-witness lines AB, BC, CA and require formTriangle a b c AB BC CA,
so that BC, CA, AB encode the three sides of △ a:b:c.

General, index-based version:
- i = 0: from vertex a to a point p on the opposite side BC (with b, p, c in that order)
         and s is exactly the segment with endpoints a and p.
- i = 1: from vertex b to a point p on the opposite side CA (with c, p, a)
- i = 2: from vertex c to a point p on the opposite side AB (with a, p, b)
Out-of-range indices map to False.
-/
@[simp] def segmentFromVertexToOppositeSideByIndex
  (T : Triangle) (AB BC CA : Line) (i : Nat) (p : Point) (s : Segment) : Prop :=
  match T with
  | Triangle.ofPoints a b c =>
    formTriangle a b c AB BC CA ∧
    match i with
    | 0 => between b p c ∧ p.onLine BC ∧ s = Segment.endpoints a p
    | 1 => between c p a ∧ p.onLine CA ∧ s = Segment.endpoints b p
    | 2 => between a p b ∧ p.onLine AB ∧ s = Segment.endpoints c p
    | _ => False

/-
Convenience aliases for the common explicit-vertex cases on △ a:b:c.

- From a to BC
- From b to CA
- From c to AB
-/
@[simp] def segmentFromAtoBC
  (a b c p : Point) (AB BC CA : Line) (s : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧ between b p c ∧ p.onLine BC ∧ s = Segment.endpoints a p

@[simp] def segmentFromBtoCA
  (a b c p : Point) (AB BC CA : Line) (s : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧ between c p a ∧ p.onLine CA ∧ s = Segment.endpoints b p

@[simp] def segmentFromCtoAB
  (a b c p : Point) (AB BC CA : Line) (s : Segment) : Prop :=
  formTriangle a b c AB BC CA ∧ between a p b ∧ p.onLine AB ∧ s = Segment.endpoints c p


/-
Extension: Midpoints, angle-bisecting segments in a triangle, points on segment extensions,
congruent segments, and perpendicular lines.

Conventions observed:
- No quantifiers (∀/∃) or disjunctions (∨).
- Explicit witnesses are provided as parameters (e.g., intersection point, chosen
  point on the opposite side of a triangle, etc.).
- Angle measures use the opaque right-angle constant ∟, as specified.
- Definitions are registered with `@[simp]`.
- Where appropriate, relations involving a "main-focus" point are placed in the `Point` namespace.
- Segment-congruence helpers are placed in a `Segment` namespace.
- For angle bisectors inside triangles, we reuse previously defined segment-from-vertex
  helpers to witness "opposite side" membership, and then assert measure equality of the split angles.
-/


/- 1) Midpoint of a segment. -/
namespace Point

/-
m is the midpoint of segment AB iff m lies between A and B and AM = MB.
-/
@[simp] def isMidpointOfPoints (m a b : Point) : Prop :=
  between a m b ∧ (|(a─m)| = |(m─b)|)

/-
Midpoint of an explicit Segment object s.
We destruct s into its endpoints to reuse isMidpointOfPoints.
-/
@[simp] def isMidpointOfSegment (m : Point) (s : Segment) : Prop :=
  match s with
  | Segment.endpoints a b => isMidpointOfPoints m a b

/-
Alias with a more concise name: m is the midpoint of AB.
-/
@[simp] def isMidpointOf (m a b : Point) : Prop :=
  isMidpointOfPoints m a b

end Point


/-
2) A line segment bisecting an angle at a vertex of a triangle.

We provide an index-based general version and concrete convenience aliases
for vertices A, B, and C of △ a:b:c. In all cases, we:
- witness that the segment goes from the chosen vertex to a point p on the
  opposite side (via segmentFromVertexToOppositeSideByIndex or its concrete aliases),
- require p to be distinct from the vertex to avoid degeneracy,
- assert equality of the two split angles at the chosen vertex.
-/

/- General, index-based version (i ∈ {0,1,2} corresponds to vertices A,B,C respectively). -/
@[simp] def segmentBisectsAngleAtVertexByIndex
  (T : Triangle) (AB BC CA : Line) (i : Nat) (p : Point) (s : Segment) : Prop :=
  match T with
  | Triangle.ofPoints a b c =>
    segmentFromVertexToOppositeSideByIndex (Triangle.ofPoints a b c) AB BC CA i p s ∧
    match i with
    | 0 => (p ≠ a) ∧ ((∠ b:a:p) = (∠ p:a:c))
    | 1 => (p ≠ b) ∧ ((∠ a:b:p) = (∠ p:b:c))
    | 2 => (p ≠ c) ∧ ((∠ a:c:p) = (∠ p:c:b))
    | _ => False

/-
Convenience aliases specialized to △ a:b:c.
-/
@[simp] def segmentFromAtoBCBisectsAngleAtA
  (a b c p : Point) (AB BC CA : Line) (s : Segment) : Prop :=
  segmentFromAtoBC a b c p AB BC CA s ∧ (p ≠ a) ∧ ((∠ b:a:p) = (∠ p:a:c))

@[simp] def segmentFromBtoCABisectsAngleAtB
  (a b c p : Point) (AB BC CA : Line) (s : Segment) : Prop :=
  segmentFromBtoCA a b c p AB BC CA s ∧ (p ≠ b) ∧ ((∠ a:b:p) = (∠ p:b:c))

@[simp] def segmentFromCtoABBisectsAngleAtC
  (a b c p : Point) (AB BC CA : Line) (s : Segment) : Prop :=
  segmentFromCtoAB a b c p AB BC CA s ∧ (p ≠ c) ∧ ((∠ a:c:p) = (∠ p:c:b))


/-
3) A point lying on the extension of a line segment beyond an endpoint.

We provide:
- Pure point-based versions: "beyond the second endpoint" means between a b x.
  "beyond the first endpoint" means between b a x.
- Line-witnessed versions requiring all three points to lie on a given line L.
- Segment-witnessed versions that destruct the segment into its endpoints.
-/
namespace Point

/-- x lies on the extension of segment AB beyond endpoint B. -/
@[simp] def onExtensionBeyondSecond (x a b : Point) : Prop :=
  between a b x

/-- x lies on the extension of segment AB beyond endpoint A. -/
@[simp] def onExtensionBeyondFirst (x a b : Point) : Prop :=
  between b a x

/-- Line-witnessed version (beyond B): A, B, X are on L and between A, B, X. -/
@[simp] def onExtensionBeyondSecondOnLine (x a b : Point) (L : Line) : Prop :=
  x.onLine L ∧ a.onLine L ∧ b.onLine L ∧ between a b x

/-- Line-witnessed version (beyond A): B, A, X are on L and between B, A, X. -/
@[simp] def onExtensionBeyondFirstOnLine (x a b : Point) (L : Line) : Prop :=
  x.onLine L ∧ a.onLine L ∧ b.onLine L ∧ between b a x

/-- Segment-witnessed version (beyond first endpoint A of s = AB). -/
@[simp] def onExtensionBeyondFirstOfSegment (x : Point) (s : Segment) : Prop :=
  match s with
  | Segment.endpoints a b => between b a x

/-- Segment-witnessed version (beyond second endpoint B of s = AB). -/
@[simp] def onExtensionBeyondSecondOfSegment (x : Point) (s : Segment) : Prop :=
  match s with
  | Segment.endpoints a b => between a b x

end Point


/-
4) Two line segments being congruent (equal length).

We provide both:
- an endpoint-based version, and
- a Segment-object version (pattern matching on endpoints).
-/
namespace Segment

@[simp] def congruentByEndpoints (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

@[simp] def congruent (s₁ s₂ : Segment) : Prop :=
  match s₁, s₂ with
  | Segment.endpoints a b, Segment.endpoints c d => |(a─b)| = |(c─d)|

end Segment


/-
5) Two lines being perpendicular.

We require explicit witnesses:
- i: the intersection point of L and M,
- u: a point on L (u ≠ i),
- v: a point on M (v ≠ i),
such that the angle ∠ u:i:v is a right angle (∟).
We also assert intersection via twoLinesIntersectAtPoint.
-/
@[simp] def perpendicularLinesAtPoint (L M : Line) (i u v : Point) : Prop :=
  twoLinesIntersectAtPoint L M i ∧
  u.onLine L ∧ v.onLine M ∧
  (u ≠ i) ∧ (v ≠ i) ∧
  ((∠ u:i:v) = ∟)


/-
Extension: Ratios of segment lengths, triangle angle sum, triangle similarity,
and convex quadrilateral (quantifier-free, no disjunctions).

This file adds the following concepts:

1) Equality of two ratios of segment lengths:
   - lengthRatiosEqualByEndpoints a b c d e f g h
     meaning |AB|/|CD| = |EF|/|GH|.
   - Segment.lengthRatiosEqual s₁ s₂ t₁ t₂ is the Segment-object version.

2) A "ratio of lengths" function:
   - lengthRatioByEndpoints a b c d : ℝ is |AB|/|CD|.
   - Segment.lengthRatio s t : ℝ is the Segment-object version.
   - Positive variants: positiveLengthRatioByEndpoints and Segment.positiveLengthRatio.

3) Triangle interior angle sum equals 180 degrees (encoded as ∟ + ∟):
   - Triangle.angleSumEqTwoRightAnglesByPoints a b c
   - Triangle.angleSumEqTwoRightAngles (for a Triangle object)

4) Triangle similarity (canonical definition):
   - trianglesSimilarByPoints a b c d e f:
     all corresponding angles equal, and all three side ratios equal
     (AB/DE = BC/EF = CA/FD).
   - trianglesSimilar T₁ T₂ is the Triangle-object version.

5) Convex quadrilateral (explicit sides; no diagonals; four non-collinear points):
   - formConvexQuadrilateral a b c d AB BC CD DA
-/

/- 1) Ratio of segment lengths: function and equality of two ratios. -/

@[simp] noncomputable def lengthRatioByEndpoints (a b c d : Point) : ℝ :=
  (|(a─b)|) / (|(c─d)|)

namespace Segment

@[simp] noncomputable def lengthRatio (s t : Segment) : ℝ :=
  match s, t with
  | Segment.endpoints a b, Segment.endpoints c d => (|(a─b)|) / (|(c─d)|)

/-- Equality of two ratios |AB|/|CD| = |EF|/|GH| via Segment objects. -/
@[simp] def lengthRatiosEqual (s₁ s₂ t₁ t₂ : Segment) : Prop :=
  lengthRatio s₁ s₂ = lengthRatio t₁ t₂

end Segment

/-- Equality of two ratios |AB|/|CD| = |EF|/|GH| via endpoints. -/
@[simp] def lengthRatiosEqualByEndpoints
  (a b c d e f g h : Point) : Prop :=
  lengthRatioByEndpoints a b c d = lengthRatioByEndpoints e f g h

/-- Positivity of a ratio of lengths via endpoints. -/
@[simp] def positiveLengthRatioByEndpoints (a b c d : Point) : Prop :=
  lengthRatioByEndpoints a b c d > 0

namespace Segment
/-- Positivity of a ratio of lengths via Segment objects. -/
@[simp] def positiveLengthRatio (s t : Segment) : Prop :=
  lengthRatio s t > 0
end Segment


/- 2) Triangle interior angle sum equals 180 degrees (encoded as ∟ + ∟). -/
namespace Triangle

/-- For points a,b,c, the interior angles at A, B, C sum to ∟ + ∟. -/
@[simp] def angleSumEqTwoRightAnglesByPoints (a b c : Point) : Prop :=
  (∠ b:a:c) + (∠ a:b:c) + (∠ a:c:b) = (∟ + ∟)

/-- For a triangle object, the interior angles sum to ∟ + ∟. -/
@[simp] def angleSumEqTwoRightAngles (T : Triangle) : Prop :=
  match T with
  | Triangle.ofPoints a b c => angleSumEqTwoRightAnglesByPoints a b c

end Triangle


/- 3) Triangle similarity (canonical definition).
All corresponding angles equal and all three corresponding side ratios equal:
AB/DE = BC/EF = CA/FD.
-/

/-- Similarity for two triangles given by their vertices a b c and d e f. -/
@[simp] def trianglesSimilarByPoints (a b c d e f : Point) : Prop :=
  anglesCongruent b a c e d f ∧
  anglesCongruent a b c d e f ∧
  anglesCongruent a c b d f e ∧
  ((|(a─b)|) / (|(d─e)|) = (|(b─c)|) / (|(e─f)|)) ∧
  ((|(b─c)|) / (|(e─f)|) = (|(c─a)|) / (|(f─d)|))

/-- Similarity for Triangle objects (uses vertex order as given). -/
@[simp] def trianglesSimilar (T₁ T₂ : Triangle) : Prop :=
  match T₁, T₂ with
  | Triangle.ofPoints a b c, Triangle.ofPoints d e f =>
      trianglesSimilarByPoints a b c d e f


/- 4) Convex quadrilateral formed by four non-collinear points with explicit sides only.

Parameters:
- a,b,c,d : vertices in cyclic order.
- AB, BC, CD, DA : lines for the four sides.

We enforce:
- Each side line contains its two vertices.
- All four points are pairwise distinct.
- Every triple of consecutive vertices is non-collinear (and also the wrap-around ones),
  ensuring no three of the four points are collinear.
- All four side lines are pairwise distinct.
- Convexity witnesses: for each side, the two non-incident vertices lie on the same side.
-/
@[simp] def formConvexQuadrilateral
  (a b c d : Point)
  (AB BC CD DA : Line) : Prop :=
  -- side incidence
  a.onLine AB ∧ b.onLine AB ∧
  b.onLine BC ∧ c.onLine BC ∧
  c.onLine CD ∧ d.onLine CD ∧
  d.onLine DA ∧ a.onLine DA ∧
  -- distinct vertices
  allDistinctPoints [a, b, c, d] ∧
  -- non-collinearity of every triple
  threePointsNonCollinear a b c ∧
  threePointsNonCollinear b c d ∧
  threePointsNonCollinear c d a ∧
  threePointsNonCollinear d a b ∧
  -- all four side lines are pairwise distinct
  (AB ≠ BC) ∧ (BC ≠ CD) ∧ (CD ≠ DA) ∧ (DA ≠ AB) ∧ (AB ≠ CD) ∧ (BC ≠ DA) ∧
  -- convexity witnesses: opposite vertices are on the same side of each side line
  c.sameSide d AB ∧
  d.sameSide a BC ∧
  a.sameSide b CD ∧
  b.sameSide c DA


/-
Extension: diagonals of a quadrilateral, general (non-triangle-specific) angle-bisecting
segment at a vertex, triangle congruence (canonical definition), triangles sharing a
common side (index/segment witnessed, no disjunctions), and equilateral triangles.

Conventions:
- No quantifiers (∀/∃) and no disjunction (∨).
- When a "choice" is needed (e.g., which diagonal, which side), we use an explicit
  numeric index to avoid disjunctions: 0/1 for the two diagonals; arbitrary indices
  i,j,k,l ∈ {0,1,2} for vertices of triangles.
- For angle measures, we keep using the opaque right-angle constant ∟ from the DSL.
- All definitions are registered under `@[simp]`.

Contents:
1) Quadrilateral side-incidence helper and diagonals
2) General angle-bisecting segment at a vertex (not restricted to triangles)
3) Triangle congruence (canonical definition)
4) Two triangles sharing a common side (index- and segment-witnessed)
5) Equilateral triangles
-/


/- 1) Quadrilateral side-incidence helper and diagonals. -/

/--
The four vertices a,b, c, d lie on the four sides AB, BC, CD, DA in cyclic order.
This captures the basic side-incidence for a quadrilateral determined by these
four lines and vertices (no convexity or non-collinearity is enforced here).
-/
@[simp] def verticesOnSidesOfQuadrilateral
  (a b c d : Point) (AB BC CD DA : Line) : Prop :=
  a.onLine AB ∧ b.onLine AB ∧
  b.onLine BC ∧ c.onLine BC ∧
  c.onLine CD ∧ d.onLine CD ∧
  d.onLine DA ∧ a.onLine DA

namespace Segment

/--
s is the AC-diagonal of the quadrilateral with vertices a,b,c,d and sides AB,BC,CD,DA.

We enforce:
- side-incidence of the four vertices,
- non-adjacency encoded by forbidding A to be on BC or CD and C to be on DA or AB,
- distinct endpoints a ≠ c,
- s equals the segment with endpoints a and c.
-/
@[simp] def isDiagonalACOfQuadrilateral
  (s : Segment) (a b c d : Point) (AB BC CD DA : Line) : Prop :=
  verticesOnSidesOfQuadrilateral a b c d AB BC CD DA ∧
  (a ≠ c) ∧
  ¬ a.onLine BC ∧ ¬ a.onLine CD ∧
  ¬ c.onLine DA ∧ ¬ c.onLine AB ∧
  s = Segment.endpoints a c

/--
s is the BD-diagonal of the quadrilateral with vertices a,b,c,d and sides AB,BC,CD,DA.

We enforce:
- side-incidence of the four vertices,
- non-adjacency encoded by forbidding B to be on CD or DA and D to be on AB or BC,
- distinct endpoints b ≠ d,
- s equals the segment with endpoints b and d.
-/
@[simp] def isDiagonalBDOfQuadrilateral
  (s : Segment) (a b c d : Point) (AB BC CD DA : Line) : Prop :=
  verticesOnSidesOfQuadrilateral a b c d AB BC CD DA ∧
  (b ≠ d) ∧
  ¬ b.onLine CD ∧ ¬ b.onLine DA ∧
  ¬ d.onLine AB ∧ ¬ d.onLine BC ∧
  s = Segment.endpoints b d

/--
Index-based diagonal selector avoiding disjunctions:
- idx = 0: AC-diagonal,
- idx = 1: BD-diagonal,
- other indices: False.

All the same side-incidence and non-adjacency conditions are enforced accordingly.
-/
@[simp] def isDiagonalOfQuadrilateralByIndex
  (s : Segment) (a b c d : Point) (AB BC CD DA : Line) (idx : Nat) : Prop :=
  verticesOnSidesOfQuadrilateral a b c d AB BC CD DA ∧
  match idx with
  | 0 =>
      (a ≠ c) ∧
      ¬ a.onLine BC ∧ ¬ a.onLine CD ∧
      ¬ c.onLine DA ∧ ¬ c.onLine AB ∧
      s = Segment.endpoints a c
  | 1 =>
      (b ≠ d) ∧
      ¬ b.onLine CD ∧ ¬ b.onLine DA ∧
      ¬ d.onLine AB ∧ ¬ d.onLine BC ∧
      s = Segment.endpoints b d
  | _ => False

end Segment


/-
2) General (non-triangle-specific) angle-bisecting segment at a vertex.

We require an explicit rectilinear angle witness via lines AB and BC,
and we ensure the endpoint p of the bisecting segment lies strictly inside
the angle by same-side tests (no disjunctions):

- p.sameSide a BC (p is on the same side of BC as a),
- p.sameSide c AB (p is on the same side of AB as c).

The segment s is exactly the segment with endpoints b and p.
-/

/--
The segment s with endpoints b and p bisects the angle ∠ a:b:c witnessed by AB and BC.

Requirements:
- formRectilinearAngle a b c AB BC (a on AB, c on BC, b is the vertex),
- p lies inside the angle: p.sameSide a BC and p.sameSide c AB,
- angle equality at the vertex: ∠ a:b:p = ∠ p:b:c,
- p ≠ b to avoid degeneracy,
- s is exactly the segment bp.
-/
@[simp] def segmentBisectsAngleAtVertex
  (a b c p : Point) (AB BC : Line) (s : Segment) : Prop :=
  formRectilinearAngle a b c AB BC ∧
  p.sameSide a BC ∧
  p.sameSide c AB ∧
  (p ≠ b) ∧
  s = Segment.endpoints b p ∧
  (∠ a:b:p) = (∠ p:b:c)


/- 3) Triangle congruence (canonical definition).

We require:
- all three corresponding sides equal in length,
- all three corresponding angles equal in measure.

Vertex correspondence:
- A ↔ D, B ↔ E, C ↔ F.
-/
@[simp] def trianglesCongruentByPoints (a b c d e f : Point) : Prop :=
  (|(a─b)| = |(d─e)|) ∧
  (|(b─c)| = |(e─f)|) ∧
  (|(c─a)| = |(f─d)|) ∧
  anglesCongruent b a c e d f ∧
  anglesCongruent a b c d e f ∧
  anglesCongruent a c b d f e

@[simp] def trianglesCongruent (T₁ T₂ : Triangle) : Prop :=
  match T₁, T₂ with
  | Triangle.ofPoints a b c, Triangle.ofPoints d e f =>
      trianglesCongruentByPoints a b c d e f


/-
4) Two triangles sharing a common side (no disjunctions).

We provide index-based helpers. Vertices are indexed as:
- 0 ↦ first vertex,
- 1 ↦ second vertex,
- 2 ↦ third vertex.

Users explicitly specify the side in each triangle via ordered vertex indices (i ≠ j) and
(k ≠ l). Orientation matters; if a reversed orientation is desired, the user should
swap the indices accordingly.
-/
namespace Triangle

/-- The i-th vertex of triangle T (out-of-range defaults to the second vertex). -/
@[simp] def vertexAt (T : Triangle) (i : Nat) : Point :=
  match T with
  | Triangle.ofPoints a b c =>
    match i with
    | 0 => a
    | 1 => b
    | 2 => c
    | _ => b

/-- The side of T determined by ordered vertices i and j, as a Segment. -/
@[simp] def sideSegmentByIndex (T : Triangle) (i j : Nat) : Segment :=
  Segment.endpoints (vertexAt T i) (vertexAt T j)

/--
s is exactly the side of T determined by ordered vertices i and j,
with the explicit requirement i ≠ j to ensure a proper side.
-/
@[simp] def isSideByIndex (T : Triangle) (i j : Nat) (s : Segment) : Prop :=
  (i ≠ j) ∧ s = Segment.endpoints (vertexAt T i) (vertexAt T j)

/--
Two triangles T₁ and T₂ share a common side witnessed by ordered indices (i,j) and (k,l)
and by the same Segment object s. Orientation matters.
-/
@[simp] def trianglesShareCommonSideByIndexWithSegment
  (T₁ T₂ : Triangle) (i j k l : Nat) (s : Segment) : Prop :=
  isSideByIndex T₁ i j s ∧ isSideByIndex T₂ k l s

/--
Two triangles T₁ and T₂ share a common side witnessed by the equalities of their
ordered endpoints (orientation matters). Explicitly requires i ≠ j and k ≠ l.
-/
@[simp] def trianglesShareSideByIndex (T₁ T₂ : Triangle) (i j k l : Nat) : Prop :=
  (i ≠ j) ∧ (k ≠ l) ∧
  vertexAt T₁ i = vertexAt T₂ k ∧
  vertexAt T₁ j = vertexAt T₂ l

end Triangle


/-
5) Equilateral triangles.

We provide both a point-based and a Triangle-object version.
-/

/-- Points a, b, c form an equilateral triangle shape iff all three sides have equal length. -/
@[simp] def triangleEquilateralByPoints (a b c : Point) : Prop :=
  (|(a─b)| = |(b─c)|) ∧ (|(b─c)| = |(c─a)|)

/-- A Triangle object is equilateral iff its three sides have equal length. -/
@[simp] def Triangle.equilateral (T : Triangle) : Prop :=
  match T with
  | Triangle.ofPoints a b c => triangleEquilateralByPoints a b c


/-
Extension: Isosceles triangles and lines intersecting two sides of a triangle
(with or without being parallel to the third side).

Conventions:
- No quantifiers (∀/∃) or disjunctions (∨).
- Users provide explicit witnesses (e.g., which vertex is the apex of the isosceles
  triangle, which side the line is parallel to, and the explicit intersection points
  on the intersected sides).
- All definitions are registered with `@[simp]`.
-/


/- 1) Isosceles triangles.

We provide point-based convenience predicates for the three possible apex vertices,
as well as Triangle-object versions with an explicit vertex index:

Index mapping for △ a:b:c:
- 0 ↦ apex at a, i.e., |AB| = |AC|
- 1 ↦ apex at b, i.e., |BA| = |BC|
- 2 ↦ apex at c, i.e., |CA| = |CB|
Out-of-range indices map to False.
-/

/-- △ a:b:c is isosceles with apex at A (i.e., |AB| = |AC|). -/
@[simp] def triangleIsoscelesAtA (a b c : Point) : Prop :=
  (|(a─b)| = |(a─c)|)

/-- △ a:b:c is isosceles with apex at B (i.e., |BA| = |BC|). -/
@[simp] def triangleIsoscelesAtB (a b c : Point) : Prop :=
  (|(b─a)| = |(b─c)|)

/-- △ a:b:c is isosceles with apex at C (i.e., |CA| = |CB|). -/
@[simp] def triangleIsoscelesAtC (a b c : Point) : Prop :=
  (|(c─a)| = |(c─b)|)

/-- Point-based index version: i = 0/1/2 corresponds to apex at A/B/C. -/
@[simp] def triangleIsoscelesByPointsAtIndex (a b c : Point) (i : Nat) : Prop :=
  match i with
  | 0 => (|(a─b)| = |(a─c)|)
  | 1 => (|(b─a)| = |(b─c)|)
  | 2 => (|(c─a)| = |(c─b)|)
  | _ => False

namespace Triangle

/-- Triangle-object version: i = 0/1/2 corresponds to apex at the 1st/2nd/3rd vertex. -/
@[simp] def isoscelesAtVertex (T : Triangle) (i : Nat) : Prop :=
  match T with
  | Triangle.ofPoints a b c =>
    match i with
    | 0 => (|(a─b)| = |(a─c)|)
    | 1 => (|(b─a)| = |(b─c)|)
    | 2 => (|(c─a)| = |(c─b)|)
    | _ => False

end Triangle


/-
2) A line intersecting two sides of a triangle and being parallel to the third side.

We require:
- a triangle witness formTriangle a b c AB BC CA,
- an explicit choice of which side it is parallel to (index 0/1/2 ↦ AB/BC/CA),
- explicit intersection points p, q with the other two sides,
- each intersection point lies between the corresponding side’s endpoints (i.e., on the side segment),
- intersections are witnessed via twoLinesIntersectAtPoint to ensure line distinctness.

Index i mapping:
- i = 0: L ∥ AB and L intersects BC at p (with between b p c) and CA at q (with between c q a).
- i = 1: L ∥ BC and L intersects AB at p (with between a p b) and CA at q (with between c q a).
- i = 2: L ∥ CA and L intersects AB at p (with between a p b) and BC at q (with between b q c).
-/
@[simp] def lineIntersectsTwoSidesAndParallelToThirdByIndex
  (a b c : Point) (AB BC CA L : Line) (i : Nat) (p q : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  match i with
  | 0 =>
      parallelLines L AB ∧
      between b p c ∧ between c q a ∧
      twoLinesIntersectAtPoint L BC p ∧
      twoLinesIntersectAtPoint L CA q
  | 1 =>
      parallelLines L BC ∧
      between a p b ∧ between c q a ∧
      twoLinesIntersectAtPoint L AB p ∧
      twoLinesIntersectAtPoint L CA q
  | 2 =>
      parallelLines L CA ∧
      between a p b ∧ between b q c ∧
      twoLinesIntersectAtPoint L AB p ∧
      twoLinesIntersectAtPoint L BC q
  | _ => False

/-
Convenience aliases for each of the three cases (no indices):
-/
@[simp] def lineIntersectsBCandCAParallelAB
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  lineIntersectsTwoSidesAndParallelToThirdByIndex a b c AB BC CA L 0 p q

@[simp] def lineIntersectsABandCAParallelBC
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  lineIntersectsTwoSidesAndParallelToThirdByIndex a b c AB BC CA L 1 p q

@[simp] def lineIntersectsABandBCParallelCA
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  lineIntersectsTwoSidesAndParallelToThirdByIndex a b c AB BC CA L 2 p q


/-
3) A line intersecting two sides of a triangle (without the parallel condition).

We provide an index-based version specifying the ordered pair of sides and explicit
intersection points p and q. Each intersection point must lie between the endpoints
of its side (i.e., on the side segment), and intersections are witnessed with
twoLinesIntersectAtPoint to ensure distinctness of lines.

Allowed ordered pairs of side indices (0/1/2 ↦ AB/BC/CA):
- (0,1), (1,0) ↦ sides AB and BC
- (1,2), (2,1) ↦ sides BC and CA
- (2,0), (0,2) ↦ sides CA and AB
All other pairs map to False.
-/
@[simp] def lineIntersectsTwoSidesOfTriangleByIndex
  (a b c : Point) (AB BC CA L : Line) (i j : Nat) (p q : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  match i, j with
  | 0, 1 =>
      between a p b ∧ between b q c ∧
      twoLinesIntersectAtPoint L AB p ∧
      twoLinesIntersectAtPoint L BC q
  | 1, 0 =>
      between b p c ∧ between a q b ∧
      twoLinesIntersectAtPoint L BC p ∧
      twoLinesIntersectAtPoint L AB q
  | 1, 2 =>
      between b p c ∧ between c q a ∧
      twoLinesIntersectAtPoint L BC p ∧
      twoLinesIntersectAtPoint L CA q
  | 2, 1 =>
      between c p a ∧ between b q c ∧
      twoLinesIntersectAtPoint L CA p ∧
      twoLinesIntersectAtPoint L BC q
  | 2, 0 =>
      between c p a ∧ between a q b ∧
      twoLinesIntersectAtPoint L CA p ∧
      twoLinesIntersectAtPoint L AB q
  | 0, 2 =>
      between a p b ∧ between c q a ∧
      twoLinesIntersectAtPoint L AB p ∧
      twoLinesIntersectAtPoint L CA q
  | _, _ => False

/-
Convenience aliases (pair-specific, no indices):
-/
@[simp] def lineIntersectsABandBCOfTriangle
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  lineIntersectsTwoSidesOfTriangleByIndex a b c AB BC CA L 0 1 p q

@[simp] def lineIntersectsBCandCAOfTriangle
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  lineIntersectsTwoSidesOfTriangleByIndex a b c AB BC CA L 1 2 p q

@[simp] def lineIntersectsCAandABOfTriangle
  (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  lineIntersectsTwoSidesOfTriangleByIndex a b c AB BC CA L 2 0 p q