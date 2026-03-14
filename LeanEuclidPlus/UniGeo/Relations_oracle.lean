import SystemE.Theory.Relations


-- ==========================================
-- two lines intersect at a point
-- ==========================================
@[simp]
abbrev twoLinesIntersectAtPoint (L1 L2 : Line) (i: Point) : Prop :=
  L1.intersectsLine L2 ∧ i.onLine L1 ∧ i.onLine L2 ∧ L1 ≠ L2


-- ==========================================
-- convex quadrilateral
-- ==========================================
@[simp]
abbrev formConvexQuadrilateral (a b c d : Point) (AB CD AC BD : Line) : Prop :=
  distinctPointsOnLine a b AB ∧
  distinctPointsOnLine c d CD ∧
  distinctPointsOnLine a c AC ∧
  distinctPointsOnLine b d BD ∧
  a.sameSide c BD ∧
  a.sameSide b CD ∧
  b.sameSide d AC ∧
  c.sameSide d AB

@[simp]
abbrev formConvexQuadrilateralWithDiagonalAD (a b c d: Point) (AB CD AC BD AD : Line) : Prop :=
  formConvexQuadrilateral a b c d AB CD AC BD ∧
  distinctPointsOnLine a d AD

@[simp]
abbrev formConvexQuadrilateralWithDiagonalBC (a b c d: Point) (AB CD AC BD BC : Line) : Prop :=
  formConvexQuadrilateral a b c d AB CD AC BD ∧
  distinctPointsOnLine b c BC

axiom convexQuadrilateralAnglesSum (a b c d : Point) (AB CD AC BD : Line) :
  formConvexQuadrilateral a b c d AB CD AC BD → ∠ a:b:d + ∠ b:d:c + ∠ d:c:a + ∠ c:a:b = ∟ + ∟ + ∟ + ∟


namespace Triangle
-- ==========================================
-- congruent triangles
-- ==========================================
-- The new definition of congruent is implemented in SystemE/Meta/Smt/UniGeo.lean
@[simp]
abbrev congruent : Triangle → Triangle →  Prop
| (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
  (|(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(A─C)| = |(D─F)| ∧
  ∠ A:B:C = ∠ D:E:F ∧ ∠ A:C:B = ∠ D:F:E ∧ ∠ B:A:C = ∠ E:D:F)

-- The new axioms for congruent are implemented in SystemE/Meta/Smt/EuclidTheory.lean
@[aesop unsafe [apply,forward]]
axiom congruent_sss (T1 T2: Triangle):
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    (Triangle.area T1 > 0) ∧ (Triangle.area T2 > 0) ∧
    |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)| → congruent T1 T2

@[aesop unsafe [apply,forward]]
axiom congruent_sas (T1 T2: Triangle):
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    (Triangle.area T1 > 0) ∧ (Triangle.area T2 > 0) ∧
    ((|(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)|) ∨
    (|(B─C)| = |(E─F)| ∧ ∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)|) ∨
    (|(C─A)| = |(F─D)| ∧ ∠ C:A:B = ∠ F:D:E ∧ |(A─B)| = |(D─E)|)) → congruent T1 T2

@[aesop unsafe [apply,forward]]
axiom congruent_asa (T1 T2: Triangle):
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    (Triangle.area T1 > 0) ∧ (Triangle.area T2 > 0) ∧
    ((∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)| ∧ ∠ B:C:A = ∠ E:F:D) ∨
    (∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)| ∧ ∠ C:A:B = ∠ F:D:E) ∨
    (∠ C:A:B = ∠ F:D:E ∧ |(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F)) → congruent T1 T2
@[aesop unsafe [apply,forward]]

axiom congruent_aas (T1 T2: Triangle):
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    (Triangle.area T1 > 0) ∧ (Triangle.area T2 > 0) ∧
    ((∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D ∧ |(A─B)| = |(D─E)|) ∨
    (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)|) ∨
    (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E ∧ |(B─C)| = |(E─F)|) ∨
    (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E ∧ |(A─B)| = |(D─E)|) ∨
    (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F ∧ |(C─A)| = |(F─D)|) ∨
    (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)|)) → congruent T1 T2

-- @[simp]
-- abbrev congruent_old : Triangle → Triangle →  Prop
-- | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
--   -- SSS
--   (|(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)|) ∨
--   -- SAS
--   (|(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)|) ∨
--   (|(B─C)| = |(E─F)| ∧ ∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)|) ∨
--   (|(C─A)| = |(F─D)| ∧ ∠ C:A:B = ∠ F:D:E ∧ |(A─B)| = |(D─E)|) ∨
-- --  ASA or AAS
--   (∠ A:B:C = ∠ D:E:F ∧ |(A─B)| = |(D─E)| ∧ ∠ B:C:A = ∠ E:F:D) ∨
--   (∠ B:C:A = ∠ E:F:D ∧ |(B─C)| = |(E─F)| ∧ ∠ C:A:B = ∠ F:D:E) ∨
--   (∠ C:A:B = ∠ F:D:E ∧ |(C─A)| = |(F─D)| ∧ ∠ A:B:C = ∠ D:E:F) ∨
--   (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D ∧ |(B─C)| = |(E─F)|) ∨
--   (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E ∧ |(C─A)| = |(F─D)|) ∨
--   (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F ∧ |(A─B)| = |(D─E)|) ∨
--   (∠ C:A:B = ∠ F:D:E ∧ ∠ B:C:A = ∠ E:F:D ∧ |(A─B)| = |(D─E)|) ∨
--   (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)|) ∨
--   (∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)| ∧ ∠ C:A:B = ∠ F:D:E)

-- @[aesop unsafe [apply,forward]]
-- axiom congruent_if (T1 T2: Triangle): congruent T1 T2 →
--   match T1,T2 with
--   | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
--     |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(A─C)| = |(D─F)| ∧ ∠ A:B:C = ∠ D:E:F ∧ ∠ A:C:B = ∠ D:F:E ∧ ∠ B:A:C = ∠ E:D:F

notation:50 a:51 "≅" b:51 => congruent a b


-- ==========================================
-- similar triangles
-- ==========================================
-- The new definition of similar is implemented in SystemE/Meta/Smt/UniGeo.lean
@[simp]
abbrev similar : Triangle → Triangle →  Prop
| (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
  (|(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧
  |(B─C)| / |(E─F)| = |(C─A)| / |(F─D)| ∧
  |(C─A)| / |(F─D)| = |(A─B)| / |(D─E)| ∧
  ∠ A:B:C = ∠ D:E:F ∧ ∠ A:C:B = ∠ D:F:E ∧ ∠ B:A:C = ∠ E:D:F)

-- The new axioms for similar are implemented in SystemE/Meta/Smt/EuclidTheory.lean
@[aesop unsafe [apply,forward]]
axiom similar_aa (T1 T2: Triangle):
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    (Triangle.area T1 > 0) ∧ (Triangle.area T2 > 0) ∧
    ((∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D) ∨
    (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E) ∨
    (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F)) → similar T1 T2

@[aesop unsafe [apply,forward]]
axiom similar_sas (T1 T2: Triangle):
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    (Triangle.area T1 > 0) ∧ (Triangle.area T2 > 0) ∧
    ((|(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧ ∠ A:B:C = ∠ D:E:F) ∨
    (|(B─C)| / |(E─F)| = |(C─A)| / |(F─D)| ∧ ∠ B:C:A = ∠ E:F:D) ∨
    (|(C─A)| / |(F─D)| = |(A─B)| / |(D─E)| ∧ ∠ C:A:B = ∠ F:D:E)) → similar T1 T2

@[aesop unsafe [apply,forward]]
axiom similar_sss (T1 T2: Triangle):
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    (Triangle.area T1 > 0) ∧ (Triangle.area T2 > 0) ∧
    (|(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧ |(B─C)| / |(E─F)| = |(C─A)| / |(F─D)|) → similar T1 T2

-- @[simp]
-- abbrev similar_old (T1 T2: Triangle): Prop :=
--   match T1, T2 with
--   | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
--   (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D) ∨
--   (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E) ∨
--   (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F) ∨
-- -- SAS criterion (with side ratios)
--   (|(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧ ∠ A:B:C = ∠ D:E:F) ∨
--   (|(B─C)| / |(E─F)| = |(C─A)| / |(F─D)| ∧ ∠ B:C:A = ∠ E:F:D) ∨
--   (|(C─A)| / |(F─D)| = |(A─B)| / |(D─E)| ∧ ∠ C:A:B = ∠ F:D:E) ∨
-- -- SSS criterion (with side ratios)
--   (|(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧ |(B─C)| / |(E─F)| = |(C─A)| / |(F─D)|)

-- notation:50 a:51 "~" b:51 => similar a b

-- @[aesop unsafe [apply,forward]]
-- axiom similar_if (T1 T2: Triangle): similar T1 T2 →
--   match T1,T2 with
--   | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
--     |(A─B)| / |(D─E)| = |(B─C)| / |(E─F)| ∧ |(A─B)| / |(D─E)| = |(B─C)| / |(E─F)|
--    ∧ |(C─A)| / |(F─D)| = |(A─B)| / |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F
--    ∧ ∠ A:C:B = ∠ D:F:E ∧ ∠ B:A:C = ∠ E:D:F

end Triangle


-- ==========================================
-- two parallel lines
-- ==========================================
@[simp]
abbrev parallel (L1 L2 : Line) : Prop :=
  ¬ L1.intersectsLine L2


-- ==========================================
-- two perpendicular lines
-- ==========================================
@[simp]
abbrev perpendicular (L1 L2 : Line) (p1 p2 i: Point) : Prop :=
  twoLinesIntersectAtPoint L1 L2 i ∧
  p1.onLine L1 ∧ p2.onLine L2 ∧
  p1 ≠ i ∧ p2 ≠ i ∧
  ∠ p1:i:p2 = ∟


-- ==========================================
-- midpoint of a line segment
-- ==========================================
@[simp]
abbrev midpoint (a b c: Point) : Prop :=
  between a b c ∧ |(a─b)| = |(b─c)|


-- ==========================================
-- supplementary angles
-- ==========================================
@[simp]
abbrev supplementaryAngles (α β : ℝ) : Prop :=
  α + β = ∟ + ∟


-- ==========================================
-- sequantially aligned points
-- ==========================================
@[simp]
alias sequentiallyAligned := between

@[simp]
def sequentiallyAlignedList (point_list : List Point) : Prop :=
  match point_list with
  | [] => True
  | [_] => True
  | [_, _] => True
  | a :: b :: c :: rest => sequentiallyAligned a b c ∧ sequentiallyAlignedList (b :: c :: rest)


-- ==========================================
-- collinear and ordered points
-- ==========================================
@[simp]
alias collinearAndOrdered := sequentiallyAligned

@[simp]
alias collinearAndOrderedList := sequentiallyAlignedList


-- ==========================================
-- mutually distinct points
-- ==========================================
@[simp]
def pointDistinctFromList (a : Point) (point_list : List Point) : Prop :=
  match point_list with
  | [] => True
  | b :: rest => a ≠ b ∧ pointDistinctFromList a rest

@[simp]
def mutuallyDistinctPointsList (point_list : List Point) : Prop :=
  match point_list with
  | [] => True
  | [_] => True
  | a :: rest => pointDistinctFromList a rest ∧ mutuallyDistinctPointsList rest


-- ==========================================
-- points on the same side of a line
-- ==========================================
@[simp]
def sameSideList (point_list : List Point) (L : Line) : Prop :=
  match point_list with
  | [] => True
  | [_] => True
  | [a, b] => a.sameSide b L
  | a :: b :: c :: rest => a.sameSide b L ∧ sameSideList (b :: c :: rest) L

@[simp]
abbrev sameSideDistinctList (point_list : List Point) (L : Line) : Prop :=
  sameSideList point_list L ∧ mutuallyDistinctPointsList point_list


-- ==========================================
-- extended point of a line segment
-- ==========================================
@[simp]
abbrev extendedPointCloserToA (a b c: Point) : Prop :=
  between c a b

@[simp]
abbrev extendedPointCloserToB (a b c: Point) : Prop :=
  between a b c


-- ==========================================
-- line bisecting an angle
-- ==========================================
@[simp]
abbrev lineBisectsAngle (a b c x: Point) (BX : Line) : Prop :=
  distinctPointsOnLine b x BX ∧
  ∠ a:b:x = ∠ c:b:x


-- ==========================================
-- equilateral triangle
-- ==========================================
@[simp]
abbrev equilateralTriangle (a b c: Point) : Prop :=
  |(a─b)| = |(b─c)| ∧ |(b─c)| = |(c─a)|
