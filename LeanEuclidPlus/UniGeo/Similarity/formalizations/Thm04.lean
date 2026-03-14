import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_4 : ∀ (E F G H I : Point) (HI IG HG EI IF EF HF GE : Line),
  formTriangle H I G HI IG HG ∧
  formTriangle E I F EI IF EF ∧
  distinctPointsOnLine H F HF ∧
  distinctPointsOnLine G E GE ∧
  twoLinesIntersectAtPoint HF GE I ∧
  between H I F ∧
  between G I E ∧
  ∠ H:G:I = ∠ F:E:I →
  (△ G:H:I).similar (△ E:F:I) :=
by
  euclid_intros
  have : ∠ E:I:F = ∠ G:I:H := by
    euclid_apply Elements.Book1.proposition_15 E G H F I GE HF
    euclid_finish
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle E F I EF FH EG ∧
-- formTriangle G H I GH FH EG ∧
-- To:
-- formTriangle H I G HI IG HG ∧
-- formTriangle E I F EI IF EF ∧
-- distinctPointsOnLine H F HF ∧
-- distinctPointsOnLine G E GE ∧
-- twoLinesIntersectAtPoint HF GE I ∧
