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
