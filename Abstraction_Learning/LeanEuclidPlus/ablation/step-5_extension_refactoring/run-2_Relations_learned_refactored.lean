import SystemE.Theory.Relations


/-!
Refactored Extension: Canonical geometric relations and utilities for 2D Euclidean Geometry.

Design goals:
- No imports; only use the DSL and Lean 4 primitives.
- No new types.
- Quantifier-free and disjunction-free.
- All new items registered under `simp`.
- Prefer the opaque right angle constant `∟`.

Highlights:
- linesMeetAtPoint: witness-based intersection at a point.
- betweennessChain: sequential between-relations along a point list.
- pairwiseAcrossOpposing / twoSetsOpposingSidesOnLine: cross-opposite-side relation for lists.
- supplementaryAngles and parallel.
- Midpoint, extensions beyond endpoints, congruent segments, perpendicular-at-a-point.
- Segment lengths and length ratios; equality of length ratios.
- Triangle angle sum (canonical statement).
- Similarity and congruence of triangles (general, degenerate allowed).
- Minimal convex quadrilateral formation.
- Quadrilateral diagonals.
- Angle bisector at a vertex (canonical).
- Triangle side selectors, shared-side witness, isosceles/equilateral triangles.
- Line cutting two sides of a triangle (with parallel variants).
-/

/-! Basic witnessed line intersection and parallelism -/

/-- Lines `L` and `M` meet at point `i` iff `i` lies on both and `L` intersects `M`. -/
@[simp]
def linesMeetAtPoint (L M : Line) (i : Point) : Prop :=
  i.onLine L ∧ i.onLine M ∧ L.intersectsLine M

/-- Two lines are parallel iff they do not intersect. -/
@[simp]
def parallel (L M : Line) : Prop :=
  ¬ L.intersectsLine M

/-- The angles ∠ a:b:c and ∠ d:e:f are supplementary iff their sum is `∟ + ∟`. -/
@[simp]
def supplementaryAngles (a b c d e f : Point) : Prop :=
  (∠ a:b:c) + (∠ d:e:f) = ∟ + ∟


/-! Sequential alignment and opposing-sides combinators on lists -/

/-- Chain of betweenness along a list:
for `a::b::c::rest`, requires `between a b c` and then recurses on `b::c::rest`.
Short lists (length ≤ 2) vacuously satisfy the chain. -/
@[simp]
def betweennessChain (pts : List Point) : Prop :=
  match pts with
  | a :: b :: c :: rest => between a b c ∧ betweennessChain (b :: c :: rest)
  | _                   => True

/-- The list has length at least 3. -/
@[simp]
def hasAtLeastThree (pts : List Point) : Prop :=
  match pts with
  | _ :: _ :: _ :: _ => True   -- 4 or more
  | _ :: _ :: _      => True   -- exactly 3
  | _                => False

/-- All points in `ys` are on the side of line `L` opposite to point `x`. -/
@[simp]
def allOpposingSidesToPoint (x : Point) (ys : List Point) (L : Line) : Prop :=
  match ys with
  | []       => True
  | y :: ys  => x.opposingSides y L ∧ allOpposingSidesToPoint x ys L

/-- For two lists `xs` and `ys`, every cross-pair (x in xs, y in ys) lies on opposing sides of `L`. -/
@[simp]
def pairwiseAcrossOpposing (xs ys : List Point) (L : Line) : Prop :=
  match xs with
  | []       => True
  | x :: xs  => allOpposingSidesToPoint x ys L ∧ pairwiseAcrossOpposing xs ys L

/-- Two sets (lists) of points lie on opposing sides of line `L`
iff every cross-pair lies on opposite sides of `L`. -/
@[simp]
def twoSetsOpposingSidesOnLine (xs ys : List Point) (L : Line) : Prop :=
  pairwiseAcrossOpposing xs ys L


/-! Midpoints, line extensions, segment congruence, and perpendicularity (witnessed) -/

namespace Point

/-- `m` is the midpoint of segment `AB` iff `A-m-B` and `|AM| = |MB|`. -/
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

/-- Segments `AB` and `CD` are congruent iff their lengths are equal. -/
@[simp]
def congruentSegments (a b c d : Point) : Prop :=
  |(a─b)| = |(c─d)|

/-- Lines `L` and `M` are perpendicular, witnessed at point `i` with points `a` on `L`
and `c` on `M`, iff:
- `L` and `M` intersect;
- `a,i,c` form a rectilinear angle with sides on `L` and `M`;
- the angle ∠ AIC is a right angle `∟`. -/
@[simp]
def perpendicularAt (L M : Line) (i a c : Point) : Prop :=
  L.intersectsLine M ∧ formRectilinearAngle a i c L M ∧ (∠ a:i:c) = ∟


/-! Segment length and ratio helpers -/

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

/-- Equality of two ratios of lengths given by endpoints:
(|AB| / |CD|) = (|EF| / |GH|). -/
@[simp]
def equalLengthRatios (a b c d e f g h : Point) : Prop :=
  (|(a─b)| / |(c─d)|) = (|(e─f)| / |(g─h)|)


/-! Triangle angle sum, similarity, and congruence (canonical, general) -/

/-- The sum of the three angles at `A`, `B`, `C` is `∟ + ∟`. -/
@[simp]
def triangleAngleSum (a b c : Point) : Prop :=
  (∠ b:a:c) + (∠ a:b:c) + (∠ a:c:b) = ∟ + ∟

/-- Triangles `ABC` and `DEF` are similar iff:
- corresponding angles are equal:
    ∠ BAC = ∠ EDF, ∠ ABC = ∠ DEF, ∠ ACB = ∠ DFE;
- corresponding sides are equally proportional (chained equalities):
    |AB|/|DE| = |BC|/|EF| and |BC|/|EF| = |CA|/|FD|.

This definition applies to degenerate and non-degenerate triangles alike. -/
@[simp]
def trianglesSimilar (a b c d e f : Point) : Prop :=
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  (|(a─b)| / |(d─e)|) = (|(b─c)| / |(e─f)|) ∧
  (|(b─c)| / |(e─f)|) = (|(c─a)| / |(f─d)|)

/-- Triangles `ABC` and `DEF` are congruent iff:
- corresponding angles are equal:
    ∠ BAC = ∠ EDF, ∠ ABC = ∠ DEF, ∠ ACB = ∠ DFE;
- corresponding sides are equal in length:
    |AB| = |DE|, |BC| = |EF|, |CA| = |FD|.

This definition applies to degenerate and non-degenerate triangles alike. -/
@[simp]
def trianglesCongruent (a b c d e f : Point) : Prop :=
  (∠ b:a:c) = (∠ e:d:f) ∧
  (∠ a:b:c) = (∠ d:e:f) ∧
  (∠ a:c:b) = (∠ d:f:e) ∧
  (|(a─b)|) = (|(d─e)|) ∧
  (|(b─c)|) = (|(e─f)|) ∧
  (|(c─a)|) = (|(f─d)|)


/-! Minimal convex quadrilateral formation -/

/-- Four points `a,b,c,d` with side-lines `AB,BC,CD,DA` form a convex quadrilateral iff:
- `a,b` lie distinctly on `AB`;
- `b,c` lie distinctly on `BC`;
- `c,d` lie distinctly on `CD`;
- `d,a` lie distinctly on `DA`;
- convexity via "same side" constraints:
    `c` and `d` are on the same side of `AB`,
    `d` and `a` are on the same side of `BC`,
    `a` and `b` are on the same side of `CD`,
    `b` and `c` are on the same side of `DA`.

No additional distinctness, non-collinearity, or intersection clauses are necessary. -/
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


/-! Quadrilateral diagonals -/

/-- `SP` is the diagonal `AC` of the ordered quadruple `(a, b, c, d)`. -/
@[simp]
def diagonalAC (a _ c _ : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints a c

/-- `SP` is the diagonal `BD` of the ordered quadruple `(a, b, c, d)`. -/
@[simp]
def diagonalBD (_ b _ d : Point) (SP : Segment) : Prop :=
  SP = Segment.endpoints b d


/-! Angle bisector at a vertex (canonical form) -/

/-- Point `p` bisects the angle at `b` with rays `BA` and `BC` iff
`∠ ABP = ∠ PBC`. -/
@[simp]
def angleBisectedBy (a b c p : Point) : Prop :=
  (∠ a:b:p) = (∠ p:b:c)


/-! Triangle side selectors, shared side, isosceles and equilateral triangles -/

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
for each triangle, when the selected side segments are definitionally equal. -/
@[simp]
def trianglesShareSideBy
    (sel₁ : Point → Point → Point → Segment)
    (sel₂ : Point → Point → Point → Segment)
    (a b c d e f : Point) : Prop :=
  sel₁ a b c = sel₂ d e f

/-- Triangle `ABC` is isosceles at `A` iff `|AB| = |AC|`. -/
@[simp]
def isoscelesAtA (a b c : Point) : Prop :=
  |(a─b)| = |(a─c)|

/-- Triangle `ABC` is isosceles at `B` iff `|BA| = |BC|`. -/
@[simp]
def isoscelesAtB (a b c : Point) : Prop :=
  |(b─a)| = |(b─c)|

/-- Triangle `ABC` is isosceles at `C` iff `|CA| = |CB|`. -/
@[simp]
def isoscelesAtC (a b c : Point) : Prop :=
  |(c─a)| = |(c─b)|

/-- Selector-based isosceles condition: the two selected sides have equal length. -/
@[simp]
def isoscelesBy
    (sel₁ sel₂ : Point → Point → Point → Segment)
    (a b c : Point) : Prop :=
  segmentLength (sel₁ a b c) = segmentLength (sel₂ a b c)

/-- Triangle `ABC` is equilateral iff `|AB| = |BC| = |CA|`
(encoded as two equalities). -/
@[simp]
def equilateralTriangle (a b c : Point) : Prop :=
  |(a─b)| = |(b─c)| ∧
  |(b─c)| = |(c─a)|


/-! A line intersecting two sides of a triangle at specified points (with parallel variants) -/

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

/-- Line `L` intersects sides `AB` and `AC` of triangle `ABC` at `p` and `q`,
and is parallel to the third side `BC`. -/
@[simp]
def lineCutsABandACParallelBC
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine CA ∧ between c q a ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine AB ∧ L.intersectsLine CA ∧
  parallel L BC

/-- Line `L` intersects sides `AB` and `BC` of triangle `ABC` at `p` and `q`,
and is parallel to the third side `CA`. -/
@[simp]
def lineCutsABandBCParallelCA
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine AB ∧ between a p b ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine AB ∧ L.intersectsLine BC ∧
  parallel L CA

/-- Line `L` intersects sides `AC` and `BC` of triangle `ABC` at `p` and `q`,
and is parallel to the third side `AB`. -/
@[simp]
def lineCutsACandBCParallelAB
    (a b c p q : Point) (AB BC CA L : Line) : Prop :=
  formTriangle a b c AB BC CA ∧
  p.onLine CA ∧ between c p a ∧
  q.onLine BC ∧ between b q c ∧
  p.onLine L ∧ q.onLine L ∧
  L.intersectsLine CA ∧ L.intersectsLine BC ∧
  parallel L AB