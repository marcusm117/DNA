import SystemE.Theory.Relations


/-
Extension: Additional geometric relations for lines, angles, and point sets.

This file adds:
- twoLinesIntersectAtPoint: two distinct lines intersecting at a specified point
- sequentiallyAlignedOnLine: three-or-more points sequentially aligned along a line (list-based)
- threePointsSequentiallyAlignedOnLine: convenience wrapper for exactly three points
- allSameSide: helper to assert a list of points are on the same side of a line as a reference point
- twoPointSetsOnOppositeSides: two nonempty lists of points lying on opposite sides of a line
- supplementaryAngles: two angles are supplementary (sum to a straight angle)
- parallelLines: two lines are parallel (distinct and do not intersect)

All definitions avoid quantifiers and disjunctions, and register under `simp`.
-/

/-- Two distinct lines L and M intersect at the explicitly given point i.
This requires the witness point i to lie on both L and M, and L ≠ M. -/
@[simp]
def twoLinesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  i.onLine L ∧ i.onLine M ∧ L ≠ M


/-- A list of points is sequentially aligned on a line L if it contains at least
three points, all lie on L, and every consecutive triple (sliding window)
has the middle point between the two neighbors.

More precisely:
- For exactly three points [a,b,c], we require `between a b c` and all three are on L.
- For four or more points [a,b,c,d, ...], we additionally require
  `between a b c` and that the tail [b,c,d, ...] is sequentially aligned on L.

This definition uses no quantifiers; it is fully recursive on the list structure. -/
@[simp]
def sequentiallyAlignedOnLine (ps : List Point) (L : Line) : Prop :=
  match ps with
  | a :: b :: c :: [] =>
      between a b c ∧ a.onLine L ∧ b.onLine L ∧ c.onLine L
  | a :: b :: c :: d :: rest =>
      (between a b c ∧ a.onLine L ∧ sequentiallyAlignedOnLine (b :: c :: d :: rest) L)
  | _ => False

/-- Convenience wrapper: exactly three points a, b, c are sequentially aligned on a line L.
This is just the base case of `sequentiallyAlignedOnLine` specialized to three points. -/
@[simp]
def threePointsSequentiallyAlignedOnLine (a b c : Point) (L : Line) : Prop :=
  sequentiallyAlignedOnLine [a, b, c] L


/-- Helper: all points in the list `ps` lie on the same side of line `L` as
the reference point `ref`. This recursively enforces `p.sameSide ref L` for each `p` in `ps`. -/
@[simp]
def allSameSide (ps : List Point) (ref : Point) (L : Line) : Prop :=
  match ps with
  | [] => True
  | p :: rest => p.sameSide ref L ∧ allSameSide rest ref L

/-- Two nonempty lists of points lie on opposing sides of a line `L`.
We take the head of each list as the representative reference point for that side.

Formally:
- If `A = a :: As` and `B = b :: Bs`, we require:
    1. `a.opposingSides b L` (the representatives are on opposite sides and not on L),
    2. every point in `As` is on the same side as `a`,
    3. every point in `Bs` is on the same side as `b`.
- If either list is empty, the relation is False. -/
@[simp]
def twoPointSetsOnOppositeSides (A B : List Point) (L : Line) : Prop :=
  match A, B with
  | a :: As, b :: Bs => a.opposingSides b L ∧ allSameSide As a L ∧ allSameSide Bs b L
  | _, _ => False


/-- Two angles (given by point triples) are supplementary if their measures sum to a straight angle,
represented canonically as `∟ + ∟`. -/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = (∟ + ∟)


/-- Two lines are parallel if they are distinct and do not intersect. -/
@[simp]
def parallelLines (L M : Line) : Prop :=
  L ≠ M ∧ ¬ L.intersectsLine M


/-
Extension: Congruent angles, non-collinearity-based triangle construction,
shared-vertex relations for triangles, triangle-vertex angles, and cevians.

This file adds:
- congruentAngles: two angles have equal measure
- nonCollinear: three points are pairwise distinct and not collinear
- triangleDefinedByNonCollinearPoints: a triangle equals Triangle.ofPoints a b c with non-collinear vertices
- trianglesShareVertex_*: nine disjunction-free cases for triangles sharing a specified common vertex
- angleAtA / angleAtB / angleAtC: the angle at each vertex of a triangle (as ℝ measures)
- segmentFromAtoSideBC / segmentFromBtoSideCA / segmentFromCtoSideAB: cevians from a vertex to an interior point of the opposite side

All definitions avoid quantifiers and disjunctions and register under `simp`.
-/

/-- Two angles (given by point triples) are congruent iff their measures are equal. -/
@[simp]
def congruentAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) = (∠ d:e:f)


/-- Three points are pairwise distinct and not collinear.
This is captured by pairwise inequalities and the failure of all three "between" orderings. -/
@[simp]
def nonCollinear (a b c : Point) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
  ¬ between a b c ∧ ¬ between b c a ∧ ¬ between c a b


/-- A triangle `T` is defined by the three non-collinear points `a, b, c`
precisely when `T = Triangle.ofPoints a b c` and the points are non-collinear. -/
@[simp]
def triangleDefinedByNonCollinearPoints (a b c : Point) (T : Triangle) : Prop :=
  T = Triangle.ofPoints a b c ∧ nonCollinear a b c


/-
Two triangles share a common vertex: disjunction-free witnesses.

We provide nine specialized relations corresponding to each possible pairing
of a vertex from the first triangle (a,b,c) with a vertex from the second (d,e,f).
Each relation takes an explicit witness point `v` and requires `v` to be equal to
the chosen vertices in both triangles.
-/

/-- Triangles abc and def share the common vertex a = d, with explicit witness v. -/
@[simp] def trianglesShareVertex_vAD (a _ _ d _ _ v : Point) : Prop := v = a ∧ v = d
/-- Triangles abc and def share the common vertex a = e, with explicit witness v. -/
@[simp] def trianglesShareVertex_vAE (a _ _ _ e _ v : Point) : Prop := v = a ∧ v = e
/-- Triangles abc and def share the common vertex a = f, with explicit witness v. -/
@[simp] def trianglesShareVertex_vAF (a _ _ _ _ f v : Point) : Prop := v = a ∧ v = f

/-- Triangles abc and def share the common vertex b = d, with explicit witness v. -/
@[simp] def trianglesShareVertex_vBD (_ b _ d _ _ v : Point) : Prop := v = b ∧ v = d
/-- Triangles abc and def share the common vertex b = e, with explicit witness v. -/
@[simp] def trianglesShareVertex_vBE (_ b _ _ e _ v : Point) : Prop := v = b ∧ v = e
/-- Triangles abc and def share the common vertex b = f, with explicit witness v. -/
@[simp] def trianglesShareVertex_vBF (_ b _ _ _ f v : Point) : Prop := v = b ∧ v = f

/-- Triangles abc and def share the common vertex c = d, with explicit witness v. -/
@[simp] def trianglesShareVertex_vCD (_ _ c d _ _ v : Point) : Prop := v = c ∧ v = d
/-- Triangles abc and def share the common vertex c = e, with explicit witness v. -/
@[simp] def trianglesShareVertex_vCE (_ _ c _ e _ v : Point) : Prop := v = c ∧ v = e
/-- Triangles abc and def share the common vertex c = f, with explicit witness v. -/
@[simp] def trianglesShareVertex_vCF (_ _ c _ _ f v : Point) : Prop := v = c ∧ v = f


/-
Angles at the vertices of a triangle (as measures in ℝ).

These are simple shorthands for the standard angle measures formed at each vertex.
-/

/-- The angle at vertex A of triangle abc is ∠ b:a:c. -/
@[simp] def angleAtA (a b c : Point) : ℝ := (∠ b:a:c)
/-- The angle at vertex B of triangle abc is ∠ a:b:c. -/
@[simp] def angleAtB (a b c : Point) : ℝ := (∠ a:b:c)
/-- The angle at vertex C of triangle abc is ∠ a:c:b. -/
@[simp] def angleAtC (a b c : Point) : ℝ := (∠ a:c:b)


/-
Cevians: segments from a vertex to a point on the opposite side.
We define the canonical "interior-point" versions, where the endpoint lies strictly
between the other two vertices (hence on the open segment, not including endpoints).
-/

/-- The segment S is the cevian from vertex A to an interior point p of side BC. -/
@[simp]
def segmentFromAtoSideBC (a b c p : Point) (S : Segment) : Prop :=
  S = Segment.endpoints a p ∧ between b p c

/-- The segment S is the cevian from vertex B to an interior point p of side CA. -/
@[simp]
def segmentFromBtoSideCA (a b c p : Point) (S : Segment) : Prop :=
  S = Segment.endpoints b p ∧ between c p a

/-- The segment S is the cevian from vertex C to an interior point p of side AB. -/
@[simp]
def segmentFromCtoSideAB (a b c p : Point) (S : Segment) : Prop :=
  S = Segment.endpoints c p ∧ between a p b


/-
Extension: Midpoints, angle-bisecting segments in triangles, extensions of segments,
congruent segments, and perpendicular lines.

This file adds:
- Point.isMidpointOf: a point is the midpoint of a segment AB (via endpoints)
- Point.isMidpointOfSegment: a point is the midpoint of a Segment, with explicit endpoints
- segmentBisectsAngleAtA / segmentBisectsAngleAtB / segmentBisectsAngleAtC:
  a segment from a vertex to an interior point of the opposite side that bisects the vertex angle
- Point.onExtensionBeyondA / Point.onExtensionBeyondB:
  a point lies on the extension of segment AB beyond endpoint A or B
- congruentSegments: two segments AB and CD are congruent (equal length)
- congruentSegments_fromEndpoints: congruent segments, with Segment arguments and explicit endpoints
- perpendicularLinesAt: two lines are perpendicular at a specified intersection point, with witnesses

All definitions avoid quantifiers and disjunctions, and register under `simp`.
-/


/-! Midpoints -/
namespace Point

/-- `m` is the midpoint of segment AB iff `m` lies between A and B and the two subsegments
have equal length. This enforces collinearity and distinctness via `between`. -/
@[simp]
def isMidpointOf (m a b : Point) : Prop :=
  between a m b ∧ |(a─m)| = |(m─b)|

/-- `m` is the midpoint of the Segment `S = AB` (explicit endpoints are provided).
This is a convenience wrapper tying the Segment witness to `isMidpointOf`. -/
@[simp]
def isMidpointOfSegment (m : Point) (S : Segment) (a b : Point) : Prop :=
  S = Segment.endpoints a b ∧ isMidpointOf m a b

end Point


/-! Angle-bisecting segments at triangle vertices -/

/-- The segment `S = a p` bisects the angle at vertex A of triangle abc.
We require:
- `nonCollinear a b c` so abc is a proper triangle,
- `between b p c` so p is on the interior of side BC,
- `S = Segment.endpoints a p` to pin down the segment,
- `∠ b:a:p = ∠ p:a:c` to express the bisector condition. -/
@[simp]
def segmentBisectsAngleAtA (a b c p : Point) (S : Segment) : Prop :=
  nonCollinear a b c ∧
  between b p c ∧
  S = Segment.endpoints a p ∧
  (∠ b:a:p) = (∠ p:a:c)

/-- The segment `S = b p` bisects the angle at vertex B of triangle abc. -/
@[simp]
def segmentBisectsAngleAtB (a b c p : Point) (S : Segment) : Prop :=
  nonCollinear a b c ∧
  between c p a ∧
  S = Segment.endpoints b p ∧
  (∠ a:b:p) = (∠ p:b:c)

/-- The segment `S = c p` bisects the angle at vertex C of triangle abc. -/
@[simp]
def segmentBisectsAngleAtC (a b c p : Point) (S : Segment) : Prop :=
  nonCollinear a b c ∧
  between a p b ∧
  S = Segment.endpoints c p ∧
  (∠ a:c:p) = (∠ p:c:b)


/-! Points on extensions of a segment beyond an endpoint -/
namespace Point

/-- Point `p` lies on the extension of segment AB beyond endpoint A
iff A is between p and B. -/
@[simp]
def onExtensionBeyondA (p a b : Point) : Prop :=
  between p a b

/-- Point `p` lies on the extension of segment AB beyond endpoint B
iff B is between A and p. -/
@[simp]
def onExtensionBeyondB (p a b : Point) : Prop :=
  between a b p

end Point


/-! Congruent segments -/

/-- Segments AB and CD are congruent iff their lengths are equal. -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

/-- Congruent segments, with Segment witnesses and explicit endpoints.
`S = AB` and `T = CD`, and `|(AB)| = |(CD)|`. -/
@[simp]
def congruentSegments_fromEndpoints (S T : Segment) (a b c d : Point) : Prop :=
  S = Segment.endpoints a b ∧
  T = Segment.endpoints c d ∧
  |(a─b)| = |(c─d)|


/-! Perpendicular lines -/

/-- Lines `L` and `M` are perpendicular at the explicitly given intersection point `i`,
witnessed by points `a ∈ L` and `c ∈ M`, precisely when:
- `i` lies on both `L` and `M` and the lines are distinct,
- `a,i,c` form a rectilinear angle with sides along `L` and `M`,
- the measure of that angle is a right angle `∟`. -/
@[simp]
def perpendicularLinesAt (L M : Line) (i a c : Point) : Prop :=
  twoLinesIntersectAtPoint L M i ∧
  formRectilinearAngle a i c L M ∧
  (∠ a:i:c) = ∟


/-
Extension: Segment-length ratios, triangle angle sum, length-ratio function,
triangle similarity, and convex quadrilaterals.

This file adds:
- lengthRatio: the ratio of lengths of two segments given by endpoints
- equalSegmentRatios: two such length ratios are equal
- triangleAngleSum: the three internal angles of triangle abc sum to a straight angle (∟ + ∟)
- trianglesSimilar: canonical definition (all corresponding angles equal and all corresponding sides in equal ratio)
- convexQuadrilateral: four points form a convex quadrilateral with explicitly provided side and diagonal lines

All definitions are quantifier-free, avoid disjunctions, and are registered under `simp`.
-/


noncomputable section

/-! Ratios of segment lengths -/

/-- The ratio of lengths of segments AB and CD, as a real number.
This is simply `|(a─b)| / |(c─d)|`. -/
@[simp]
def lengthRatio (a b c d : Point) : ℝ :=
  |(a─b)| / |(c─d)|

/-- Two ratios of segment lengths are equal:
`|(a─b)| / |(c─d)| = |(e─f)| / |(g─h)|`. -/
@[simp]
def equalSegmentRatios (a b c d e f g h : Point) : Prop :=
  lengthRatio a b c d = lengthRatio e f g h


/-! Triangle angle sum -/

/-- The three internal angles of triangle `abc` (with non-collinear vertices) sum to a straight angle.
The straight angle is canonically represented as `∟ + ∟`. -/
@[simp]
def triangleAngleSum (a b c : Point) : Prop :=
  nonCollinear a b c ∧
  angleAtA (a) (b) (c) + angleAtB (a) (b) (c) + angleAtC (a) (b) (c) = (∟ + ∟)


/-! Triangle similarity (canonical definition) -/

/-- Triangles `abc` and `def` are similar if:
1. both have non-collinear vertices,
2. all corresponding angles are equal (A↔D, B↔E, C↔F),
3. all corresponding sides are in equal ratio, expressed by chained equalities:
   `AB/DE = BC/EF = CA/FD` (encoded as two equalities).

The vertex correspondence is fixed as: `a ↔ d`, `b ↔ e`, `c ↔ f`. -/
@[simp]
def trianglesSimilar (a b c d e f : Point) : Prop :=
  nonCollinear a b c ∧
  nonCollinear d e f ∧
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  lengthRatio a b d e = lengthRatio b c e f ∧
  lengthRatio b c e f = lengthRatio c a f d

end


/-! Convex quadrilateral defined by four non-collinear points -/

/-- The points `a, b, c, d` (in this cyclic order) together with explicit side lines `AB, BC, CD, DA`
and diagonals `AC, BD` form a convex quadrilateral when:

- the four vertices are pairwise distinct,
- adjacent vertex pairs lie on the corresponding side lines (`distinctPointsOnLine`),
- the diagonals are the lines through the non-adjacent vertex pairs (`distinctPointsOnLine`),
- the four side lines are all distinct (including opposite sides),
- the diagonals intersect,
- vertices `b` and `d` lie on the same side of the diagonal `AC`,
- vertices `a` and `c` lie on the same side of the diagonal `BD`.

These conditions rule out self-intersection and guarantee convexity without any quantifiers or disjunctions. -/
@[simp]
def convexQuadrilateral
    (a b c d : Point)
    (AB BC CD DA AC BD : Line) : Prop :=
  -- distinct vertices
  a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
  -- sides with explicit lines
  distinctPointsOnLine a b AB ∧
  distinctPointsOnLine b c BC ∧
  distinctPointsOnLine c d CD ∧
  distinctPointsOnLine d a DA ∧
  -- diagonals with explicit lines
  distinctPointsOnLine a c AC ∧
  distinctPointsOnLine b d BD ∧
  -- all side lines are distinct
  AB ≠ BC ∧ BC ≠ CD ∧ CD ≠ DA ∧ DA ≠ AB ∧ AB ≠ CD ∧ BC ≠ DA ∧
  -- diagonals intersect (interior intersection is abstracted by this primitive)
  (AC.intersectsLine BD) ∧
  -- convexity via same-side tests
  b.sameSide d AC ∧
  a.sameSide c BD


/-
Extension: Diagonals of quadrilaterals, general angle-bisecting segments,
triangle congruence, triangles sharing a common side, and equilateral triangles.

This file adds:
- diagonalOfQuadrilateral_AC / diagonalOfQuadrilateral_BD:
  a segment is a diagonal of a quadrilateral (witnessed by endpoints across AC or BD)
- segmentBisectsAngleAtVertex:
  a segment from the vertex bisects a rectilinear angle with explicit side-lines
- trianglesCongruent:
  canonical definition (all corresponding angles equal and all corresponding sides equal)
- trianglesShareSide_*:
  nine disjunction-free cases for triangles sharing a specified common side, with an explicit segment witness
- triangleEquilateral:
  a triangle has all three sides equal (non-collinear vertices)

All definitions avoid quantifiers and disjunctions, and register under `simp`.
-/


/-! Diagonals of a quadrilateral (as segments) -/

/-- The segment `S` is the diagonal across vertices `a` and `c` of the quadrilateral
with vertices in cyclic order `a, b, c, d`. This captures the canonical notion that
a diagonal connects two non-adjacent vertices. -/
@[simp]
def diagonalOfQuadrilateral_AC (a _ c _ : Point) (S : Segment) : Prop :=
  S = Segment.endpoints a c ∧ a ≠ c

/-- The segment `S` is the diagonal across vertices `b` and `d` of the quadrilateral
with vertices in cyclic order `a, b, c, d`. -/
@[simp]
def diagonalOfQuadrilateral_BD (_ b _ d : Point) (S : Segment) : Prop :=
  S = Segment.endpoints b d ∧ b ≠ d



/-! A segment bisecting an angle at its vertex (general, with explicit side lines) -/

/-- The segment `S = v p` bisects the angle at vertex `v` formed by lines `L₁` and `L₂`,
with reference points `a ∈ L₁` and `c ∈ L₂`.

We require:
- the vertex `v` lies on both side-lines `L₁` and `L₂`,
- `a` lies on `L₁` and `c` lies on `L₂` (so that the angle is witnessed by points),
- `S = Segment.endpoints v p`,
- `p` is in the interior of the angle: it is not on either side-line and
  lies on the same side of `L₂` as `a`, and on the same side of `L₁` as `c`,
- the bisector condition `(∠ a:v:p) = (∠ p:v:c)` holds. -/
@[simp]
def segmentBisectsAngleAtVertex
    (a v c p : Point) (L₁ L₂ : Line) (S : Segment) : Prop :=
  v.onLine L₁ ∧ v.onLine L₂ ∧
  a.onLine L₁ ∧ c.onLine L₂ ∧
  S = Segment.endpoints v p ∧
  ¬ p.onLine L₁ ∧ ¬ p.onLine L₂ ∧
  p.sameSide a L₂ ∧
  p.sameSide c L₁ ∧
  (∠ a:v:p) = (∠ p:v:c)



/-! Triangle congruence (canonical definition) -/

/-- Triangles `abc` and `def` are congruent if:
1. both have non-collinear vertices,
2. all corresponding angles are equal (A↔D, B↔E, C↔F),
3. all corresponding sides are equal (AB=DE, BC=EF, CA=FD).

The vertex correspondence is fixed as: `a ↔ d`, `b ↔ e`, `c ↔ f`. -/
@[simp]
def trianglesCongruent (a b c d e f : Point) : Prop :=
  nonCollinear a b c ∧
  nonCollinear d e f ∧
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  |(a─b)| = |(d─e)| ∧
  |(b─c)| = |(e─f)| ∧
  |(c─a)| = |(f─d)|



/-! Two triangles sharing a common side (disjunction-free cases with a witness segment) -/

/-- Triangles `abc` and `def` share the side `AB = DE`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_AB_DE (a b _ d e _ : Point) (S : Segment) : Prop :=
  S = Segment.endpoints a b ∧ S = Segment.endpoints d e
/-- Triangles `abc` and `def` share the side `AB = EF`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_AB_EF (a b _ _ e f : Point) (S : Segment) : Prop :=
  S = Segment.endpoints a b ∧ S = Segment.endpoints e f
/-- Triangles `abc` and `def` share the side `AB = FD`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_AB_FD (a b _ d _ f : Point) (S : Segment) : Prop :=
  S = Segment.endpoints a b ∧ S = Segment.endpoints f d

/-- Triangles `abc` and `def` share the side `BC = DE`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_BC_DE (_ b c d e _ : Point) (S : Segment) : Prop :=
  S = Segment.endpoints b c ∧ S = Segment.endpoints d e
/-- Triangles `abc` and `def` share the side `BC = EF`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_BC_EF (_ b c _ e f : Point) (S : Segment) : Prop :=
  S = Segment.endpoints b c ∧ S = Segment.endpoints e f
/-- Triangles `abc` and `def` share the side `BC = FD`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_BC_FD (_ b c d _ f : Point) (S : Segment) : Prop :=
  S = Segment.endpoints b c ∧ S = Segment.endpoints f d

/-- Triangles `abc` and `def` share the side `CA = DE`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_CA_DE (a _ c d e _ : Point) (S : Segment) : Prop :=
  S = Segment.endpoints c a ∧ S = Segment.endpoints d e
/-- Triangles `abc` and `def` share the side `CA = EF`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_CA_EF (a _ c _ e f : Point) (S : Segment) : Prop :=
  S = Segment.endpoints c a ∧ S = Segment.endpoints e f
/-- Triangles `abc` and `def` share the side `CA = FD`, with explicit segment witness `S`. -/
@[simp] def trianglesShareSide_CA_FD (a _ c d _ f : Point) (S : Segment) : Prop :=
  S = Segment.endpoints c a ∧ S = Segment.endpoints f d



/-! Equilateral triangles -/

/-- Triangle `abc` is equilateral if its vertices are non-collinear and all three sides are equal:
`AB = BC = CA` (encoded as two equalities). -/
@[simp]
def triangleEquilateral (a b c : Point) : Prop :=
  nonCollinear a b c ∧
  |(a─b)| = |(b─c)| ∧
  |(b─c)| = |(c─a)|


/-
Extension: Isosceles triangles and lines intersecting two sides of a triangle.

This file adds:
- triangleIsoscelesAtA / triangleIsoscelesAtB / triangleIsoscelesAtC:
  a triangle is isosceles with the specified vertex as apex
- lineIntersectsTwoSides_*:
  three disjunction-free variants stating a line meets two specified sides of a triangle
  at given interior points (betweenness witnesses)
- lineIntersectsTwoSides_parallelThird_*:
  three disjunction-free variants additionally requiring the line to be parallel to the
  remaining third side

All definitions avoid quantifiers and disjunctions, and register under `simp`.
-/


/-! Isosceles triangles (by apex) -/

/-- Triangle `abc` is isosceles with apex at `A` (i.e., `AB = AC`).
We also require `a, b, c` to be non-collinear to ensure a proper triangle. -/
@[simp]
def triangleIsoscelesAtA (a b c : Point) : Prop :=
  nonCollinear a b c ∧ |(a─b)| = |(a─c)|

/-- Triangle `abc` is isosceles with apex at `B` (i.e., `BA = BC`). -/
@[simp]
def triangleIsoscelesAtB (a b c : Point) : Prop :=
  nonCollinear a b c ∧ |(b─a)| = |(b─c)|

/-- Triangle `abc` is isosceles with apex at `C` (i.e., `CA = CB`). -/
@[simp]
def triangleIsoscelesAtC (a b c : Point) : Prop :=
  nonCollinear a b c ∧ |(c─a)| = |(c─b)|



/-! A line intersecting two sides of a triangle (with explicit interior intersection points) -/

/-- The line `L` intersects sides `AB` and `AC` of triangle `abc` at interior points `p` and `q`
(respectively), with explicit side-lines and triangle witness.

We require:
- `formTriangle a b c AB BC CA` (side-lines are explicitly provided),
- `p` is the intersection of `AB` and `L`, and lies between `a` and `b`,
- `q` is the intersection of `CA` and `L`, and lies between `a` and `c`,
- the two intersection points are distinct. -/
@[simp]
def lineIntersectsTwoSides_AB_AC
    (a b c : Point) (AB BC CA L : Line) (p q : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  twoLinesIntersectAtPoint AB L p ∧ between a p b ∧
  twoLinesIntersectAtPoint CA L q ∧ between a q c ∧
  p ≠ q

/-- The line `L` intersects sides `AB` and `BC` of triangle `abc` at interior points `p` and `q`
(respectively), with explicit side-lines and triangle witness. -/
@[simp]
def lineIntersectsTwoSides_AB_BC
    (a b c : Point) (AB BC CA L : Line) (p q : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  twoLinesIntersectAtPoint AB L p ∧ between a p b ∧
  twoLinesIntersectAtPoint BC L q ∧ between b q c ∧
  p ≠ q

/-- The line `L` intersects sides `BC` and `CA` of triangle `abc` at interior points `p` and `q`
(respectively), with explicit side-lines and triangle witness. -/
@[simp]
def lineIntersectsTwoSides_BC_CA
    (a b c : Point) (AB BC CA L : Line) (p q : Point) : Prop :=
  formTriangle a b c AB BC CA ∧
  twoLinesIntersectAtPoint BC L p ∧ between b p c ∧
  twoLinesIntersectAtPoint CA L q ∧ between c q a ∧
  p ≠ q



/-! A line intersecting two sides and parallel to the third side -/

/-- The line `L` intersects sides `AB` and `AC` of triangle `abc` at interior points `p` and `q`,
and is parallel to the third side `BC`. -/
@[simp]
def lineIntersectsTwoSides_parallelThird_AB_AC_BC
    (a b c : Point) (AB BC CA L : Line) (p q : Point) : Prop :=
  lineIntersectsTwoSides_AB_AC a b c AB BC CA L p q ∧
  parallelLines L BC

/-- The line `L` intersects sides `AB` and `BC` of triangle `abc` at interior points `p` and `q`,
and is parallel to the third side `CA`. -/
@[simp]
def lineIntersectsTwoSides_parallelThird_AB_BC_CA
    (a b c : Point) (AB BC CA L : Line) (p q : Point) : Prop :=
  lineIntersectsTwoSides_AB_BC a b c AB BC CA L p q ∧
  parallelLines L CA

/-- The line `L` intersects sides `BC` and `CA` of triangle `abc` at interior points `p` and `q`,
and is parallel to the third side `AB`. -/
@[simp]
def lineIntersectsTwoSides_parallelThird_BC_CA_AB
    (a b c : Point) (AB BC CA L : Line) (p q : Point) : Prop :=
  lineIntersectsTwoSides_BC_CA a b c AB BC CA L p q ∧
  parallelLines L AB