import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_1 : ∀ (E F G H I : Point) (EF FG EG HI IG HG HF EI : Line),
  formTriangle E F G EF FG EG ∧
  formTriangle H I G HI IG HG ∧
  distinctPointsOnLine H F HF ∧
  distinctPointsOnLine E I EI ∧
  twoLinesIntersectAtPoint HF EI G ∧
  between H G F ∧
  between E G I ∧
  ∠ H:I:G = ∠ E:F:G →
  (△ G:H:I).similar (△ G:E:F) :=
by
  euclid_intros
  have : ∠ E:G:F = ∠ H:G:I := by
    euclid_apply Elements.Book1.proposition_15 E I H F G EI HF
    euclid_finish
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle E F G EF FH EI ∧
-- formTriangle H I G HI EI FH ∧
-- To:
-- formTriangle E F G EF FG EG ∧
-- formTriangle H I G HI IG HG ∧
-- distinctPointsOnLine H F HF ∧
-- distinctPointsOnLine E I EI ∧
-- twoLinesIntersectAtPoint HF EI G ∧
