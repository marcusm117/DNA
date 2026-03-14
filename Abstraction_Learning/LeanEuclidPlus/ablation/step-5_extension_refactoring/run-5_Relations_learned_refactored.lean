import SystemE.Theory.Relations


/-!
Refactored Extension: Canonical geometric relations and list-based combinators for 2D Euclidean Geometry.

Design goals:
- Eliminate redundancy by relying on core DSL primitives (e.g., between, formTriangle).
- Generalize definitions to maximize reuse and allow degenerate cases where appropriate.
- Keep definitions quantifier-free and without disjunctions.
- Prefer the right-angle constant ∟ for angle measures.
- Register all new APIs with `@[simp]`.

Contents:
1. List-based helpers: allOnLine, betweennessChain, hasAtLeastThree.
2. Intersections, alignment, opposing-sides families:
   - linesIntersectAtPoint
   - sequentiallyAlignedOnLine / sequentiallyAlignedThreeOrMore
   - allOpposingSidesToPoint / pairwiseAcrossOpposing / twoSetsOpposingSidesOnLine
   - supplementaryAngles
   - parallel
3. Segments, midpoints, extensions, perpendicularity:
   - segmentFromPointToBetween
   - Point.isMidpointOf / Point.isMidpointOfSegmentEndpoints
   - Point.onExtensionBeyondA / Point.onExtensionBeyondB
   - congruentSegments / congruentSegmentsBy
   - perpendicularAt
4. Segment length and length ratios:
   - segmentLength
   - equalLengthRatios / equalLengthRatiosBySegments
5. Triangles:
   - triangleAngleSum (via formTriangle)
   - trianglesSimilar (angles and side-ratio equalities; allows degeneracy)
   - trianglesCongruent (angles and side equalities; allows degeneracy)
   - Triangle.sideAB / Triangle.sideBC / Triangle.sideCA
   - trianglesShareSideBy
   - equilateralTriangle
   - isoscelesAtA / isoscelesAtB / isoscelesAtC / isoscelesBy
   - lineCutsTriangle...At (three variants)
   - lineCuts...Parallel... (three variants)
6. Convex quadrilateral:
   - formConvexQuadrilateral (minimal, using side membership and same-side constraints)
-/

/-! List-based helpers (quantifier-free "for all in list" patterns) -/

/-- Every point in a list lies on a given line. -/
@[simp]
def allOnLine (pts : List Point) (L : Line) : Prop :=
  match pts with
  | []       => True
  | x :: xs  => x.onLine L ∧ allOnLine xs L

/-- Betweenness chain along a point list:
for a::b::c::rest, requires between a b c and then recurses on b::c::rest. -/
@[simp]
def betweennessChain (pts : List Point) : Prop :=
  match pts with
  | a :: b :: c :: rest => between a b c ∧ betweennessChain (b :: c :: rest)
  | _                   => True

/-- The list contains at least three points. -/
@[simp]
def hasAtLeastThree (pts : List Point) : Prop :=
  match pts with
  | _ :: _ :: _ :: _ => True   -- 4 or more
  | _ :: _ :: _      => True   -- exactly 3
  | _                => False


/-! Intersections, alignment, opposing-sides, supplementary, and parallel -/

/-- Two lines intersect at point `i` iff `i` lies on both lines. -/
@[simp]
def linesIntersectAtPoint (L M : Line) (i : Point) : Prop :=
  i.onLine L ∧ i.onLine M

/-- A list of points is sequentially aligned on line `L` if all points lie on `L`
and consecutive triples satisfy the betweenness chain. No extra distinctness clauses
are added since `between` already enforces distinctness and collinearity locally. -/
@[simp]
def sequentiallyAlignedOnLine (pts : List Point) (L : Line) : Prop :=
  allOnLine pts L ∧ betweennessChain pts

/-- As above, with the additional requirement that the list has at least three points. -/
@[simp]
def sequentiallyAlignedThreeOrMore (pts : List Point) (L : Line) : Prop :=
  hasAtLeastThree pts ∧ sequentiallyAlignedOnLine pts L

/-- All points in `ys` are on the side of line `L` opposite to point `x`. -/
@[simp]
def allOpposingSidesToPoint (x : Point) (ys : List Point) (L : Line) : Prop :=
  match ys with
  | []       => True
  | y :: ys  => x.opposingSides y L ∧ allOpposingSidesToPoint x ys L

/-- For lists `xs` and `ys`, every cross-pair (x ∈ xs, y ∈ ys) lies on opposing sides of line `L`. -/
@[simp]
def pairwiseAcrossOpposing (xs ys : List Point) (L : Line) : Prop :=
  match xs with
  | []       => True
  | x :: xs  => allOpposingSidesToPoint x ys L ∧ pairwiseAcrossOpposing xs ys L

/-- Two sets (lists) of points lie on opposing sides of line `L` iff every cross-pair
is on opposite sides of `L`. Auxiliary "not on line" requirements are omitted since
`Point.opposingSides` already excludes points on the line. -/
@[simp]
def twoSetsOpposingSidesOnLine (xs ys : List Point) (L : Line) : Prop :=
  pairwiseAcrossOpposing xs ys L

/-- Two angles ∠ a:b:c and ∠ d:e:f are supplementary iff their sum is ∟ + ∟. -/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = ∟ + ∟

/-- Two lines are parallel if they are distinct and non-intersecting. -/
@[simp]
def parallel (L M : Line) : Prop :=
  L ≠ M ∧ ¬ L.intersectsLine M


/-! Segments, midpoints, extensions, perpendicularity -/

/-- Segment `SP` joins `v` to point `p` that lies between `s1` and `s2`. -/
@[simp]
def segmentFromPointToBetween (v s1 s2 p : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints v p ∧ between s1 p s2

namespace Point

/-- `m` is the midpoint of segment `AB` iff `A-m-B` and `|AM| = |MB|`. -/
@[simp]
def isMidpointOf (m a b : Point) : Prop :=
  between a m b ∧ |(a─m)| = |(m─b)|

/-- Midpoint with an explicit segment witness `SP = [a,b]`. -/
@[simp]
def isMidpointOfSegmentEndpoints (m a b : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints a b ∧ isMidpointOf m a b

/-- `p` lies on the extension of segment `AB` beyond endpoint `B` iff `A-B-P`. -/
@[simp]
def onExtensionBeyondB (p a b : Point) : Prop :=
  between a b p

/-- `p` lies on the extension of segment `AB` beyond endpoint `A` iff `B-A-P`. -/
@[simp]
def onExtensionBeyondA (p a b : Point) : Prop :=
  between b a p

end Point

/-- Segments `[a,b]` and `[c,d]` are congruent iff their lengths are equal. -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

/-- Congruent segments with explicit segment witnesses `SP1 = [a,b]` and `SP2 = [c,d]`. -/
@[simp]
def congruentSegmentsBy (SP1 SP2 : Segment) (a b c d : Point) : Prop :=
  SP1 = Segment.endpoints a b ∧ SP2 = Segment.endpoints c d ∧ congruentSegments a b c d

/-- Lines `L` and `M` are perpendicular at `i` with witnesses `a` on `L` and `c` on `M`
iff they form a rectilinear angle at `i` of measure ∟. -/
@[simp]
def perpendicularAt (L M : Line) (i a c : Point) : Prop :=
  L.intersectsLine M ∧ formRectilinearAngle a i c L M ∧ (∠ a:i:c) = ∟


/-! Segment length and length ratios -/

/-- The length of a segment. -/
@[simp]
def segmentLength (SP : Segment) : ℝ :=
  match SP with
  | Segment.endpoints a b => |(a─b)|

/-- Equality of two ratios of lengths given by endpoints:
(|AB| / |CD|) = (|EF| / |GH|). -/
@[simp]
def equalLengthRatios (a b c d e f g h : Point) : Prop :=
  (|(a─b)| / |(c─d)|) = (|(e─f)| / |(g─h)|)

/-- Equality of two ratios of lengths using segment witnesses. -/
@[simp]
def equalLengthRatiosBySegments (SP1 SP2 SP3 SP4 : Segment) : Prop :=
  segmentLength SP1 / segmentLength SP2 = segmentLength SP3 / segmentLength SP4


/-! Triangle properties and relations -/

/-- For a triangle `ABC` formed by lines `AB`, `BC`, `CA`, the three interior angles sum to ∟ + ∟. -/
@[simp]
def triangleAngleSum (a b c : Point) (AB BC CA : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  ((∠ b:a:c) + (∠ a:b:c) + (∠ a:c:b) = ∟ + ∟)

/-- Triangles `ABC` and `DEF` are similar iff all corresponding angles are equal
and corresponding side-length ratios are equal (encoded as a chain of equalities).
Degenerate triangles are allowed. -/
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
and all corresponding sides are equal. Degenerate triangles are allowed. -/
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

/-- Two triangles `ABC` and `DEF` share a common side when the chosen side-selectors
return equal segments. Typical selectors are `Triangle.sideAB`, `Triangle.sideBC`, or `Triangle.sideCA`. -/
@[simp]
def trianglesShareSideBy
    (sel₁ : Point → Point → Point → Segment)
    (sel₂ : Point → Point → Point → Segment)
    (a b c d e f : Point) : Prop :=
  sel₁ a b c = sel₂ d e f

/-- Triangle `ABC` is equilateral iff all three side lengths are equal
(encoded as two equalities). Degenerate triangles are allowed. -/
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

/-- Selector-based isosceles condition: the two selected sides of `ABC` have equal length. -/
@[simp]
def isoscelesBy
    (sel₁ sel₂ : Point → Point → Point → Segment)
    (a b c : Point) : Prop :=
  segmentLength (sel₁ a b c) = segmentLength (sel₂ a b c)


/-! Angle bisectors at a vertex -/

/-- Segment `BP` bisects angle ABC at vertex `b`, with lines `AB`, `BC` as sides
and `BP` as the carrier line for the bisector. The point `p` is inside the angle,
witnessed by same-side constraints. `SP` is the segment `[b,p]`. -/
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


/-! A line intersecting sides of a triangle at specified points -/

/-- Line `L` cuts sides `AB` and `AC` of triangle `ABC` at `p` and `q` respectively.
Requires `formTriangle a b c AB BC CA`. Betweenness witnesses interior intersection. -/
@[simp]
def lineCutsTriangleOnABandACAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine CA ∧ between c q a ∧
  p.onLine L ∧ q.onLine L

/-- Line `L` cuts sides `AB` and `BC` of triangle `ABC` at `p` and `q` respectively. -/
@[simp]
def lineCutsTriangleOnABandBCAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L

/-- Line `L` cuts sides `AC` and `BC` of triangle `ABC` at `p` and `q` respectively. -/
@[simp]
def lineCutsTriangleOnACandBCAt
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧ between c p a ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L


/-! The above scenarios with the cutting line parallel to the third side -/

/-- Line `L` cuts sides `AB` and `AC` at `p` and `q` and is parallel to side `BC`. -/
@[simp]
def lineCutsABandACParallelBC
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine CA ∧ between c q a ∧
  p.onLine L ∧ q.onLine L ∧
  parallel L BC

/-- Line `L` cuts sides `AB` and `BC` at `p` and `q` and is parallel to side `CA`. -/
@[simp]
def lineCutsABandBCParallelCA
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  parallel L CA

/-- Line `L` cuts sides `AC` and `BC` at `p` and `q` and is parallel to side `AB`. -/
@[simp]
def lineCutsACandBCParallelAB
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧ between c p a ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  parallel L AB


/-! Convex quadrilateral -/

/-- Four points `a,b,c,d` with side-lines `AB,BC,CD,DA` form a convex quadrilateral if:
- consecutive vertices lie on their given side lines with distinct endpoints, and
- each pair of nonincident vertices lies on the same side of the opposite side line.
No additional distinctness, non-collinearity, or intersection clauses are included,
since `distinctPointsOnLine` and `sameSide` already enforce the needed constraints. -/
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