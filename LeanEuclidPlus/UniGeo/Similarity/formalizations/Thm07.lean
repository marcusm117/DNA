import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_7 : ∀ (E F G H I : Point) (EF FG EG HI IG HG FH EI: Line),
  formTriangle E F G EF FG EG ∧
  formTriangle H I G HI IG HG ∧
  distinctPointsOnLine F H FH ∧
  distinctPointsOnLine E I EI ∧
  twoLinesIntersectAtPoint FH EI G ∧
  between E G I ∧
  between F G H ∧
  |(F─G)| / |(G─H)| = |(E─G)| / |(G─I)| →
  (△ E:F:G).similar (△ I:H:G) :=
by
  euclid_intros

  have : ∠ F:G:E = ∠ H:G:I := by
    euclid_apply Elements.Book1.proposition_15 E I H F G EI FH
    euclid_finish

  apply Triangle.similar_sas (△ E:F:G) (△ I:H:G)
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle E F G EF FH EI ∧
-- formTriangle H I G HI EI FH ∧
-- To:
-- formTriangle E F G EF FG EG ∧
-- formTriangle H I G HI IG HG ∧
-- distinctPointsOnLine F H FH ∧
-- distinctPointsOnLine E I EI ∧
-- twoLinesIntersectAtPoint FH EI G ∧
