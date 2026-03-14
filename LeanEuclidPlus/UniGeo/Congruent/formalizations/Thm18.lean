import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_18 : ∀ (E F G H I : Point) (GI IF FG HE EI IH FH GE : Line),
  formTriangle G I F GI IF FG ∧
  formTriangle H E I HE EI IH ∧
  distinctPointsOnLine F H FH ∧
  distinctPointsOnLine G E GE ∧
  twoLinesIntersectAtPoint FH GE I ∧
  between F I H ∧
  between E I G ∧
  |(E─I)| = |(G─I)| ∧
  ¬ HE.intersectsLine FG →
  |(H─I)| = |(F─I)| :=
by
  euclid_intros
  have : ∠ I:E:H = ∠ I:G:F := by
    euclid_apply Elements.Book1.proposition_29''' F H G E FG HE GE
    euclid_finish
  have : ∠ I:F:G = ∠ I:H:E := by
    euclid_apply Elements.Book1.proposition_29''' G E F H FG HE FH
    euclid_finish
  euclid_assert (△ E:H:I).congruent (△ G:F:I)
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle E H I EH FH EG ∧
-- formTriangle F G I FG EG FH ∧
-- To:
-- formTriangle G I F GI IF FG ∧
-- formTriangle H E I HE EI IH ∧
-- distinctPointsOnLine F H FH ∧
-- distinctPointsOnLine G E GE ∧
-- twoLinesIntersectAtPoint FH GE I ∧
