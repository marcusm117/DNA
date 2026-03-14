import SystemE
import Book.Prop15
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_2 : ∀ (R S T U V : Point) (ST TR SR UV VR UR TU SV: Line),
  formTriangle S T R ST TR SR ∧
  formTriangle U V R UV VR UR ∧
  distinctPointsOnLine T U TU ∧
  distinctPointsOnLine S V SV ∧
  twoLinesIntersectAtPoint TU SV R ∧
  between T R U ∧
  between S R V ∧
  ¬ UV.intersectsLine ST →
  (△ R:U:V).similar (△ R:T:S) :=
by
  euclid_intros
  have : ∠ S:R:T = ∠ U:R:V := by
    euclid_apply Elements.Book1.proposition_15 T U V S R TU SV
    euclid_finish
  have : ∠ V:U:R = ∠ R:T:S := by
    euclid_apply Elements.Book1.proposition_29''' V S U T UV ST TU
    euclid_finish
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle S T R ST TU SV ∧
-- formTriangle U V R UV SV TU ∧
-- To:
-- formTriangle S T R ST TR SR ∧
-- formTriangle U V R UV VR UR ∧
-- distinctPointsOnLine T U TU ∧
-- distinctPointsOnLine S V SV ∧
-- twoLinesIntersectAtPoint TU SV R ∧
