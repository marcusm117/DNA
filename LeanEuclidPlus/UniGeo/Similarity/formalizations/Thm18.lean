import SystemE
import Book.Prop32
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_18 : ∀ (T U V W : Point) (UV VW UW WT : Line),
  formTriangle V W U VW UW UV ∧
  distinctPointsOnLine W T WT ∧
  twoLinesIntersectAtPoint WT UV T ∧
  between U T V ∧
  ∠ V:W:U = ∟ ∧
  ∠ W:T:U = ∟ →
  (△ T:U:W).similar (△ T:W:V) :=
by
  euclid_intros
  -- euclid_assert ∠ U:T:W = ∠ V:T:W
  have : ∠ W:V:U + ∠ V:U:W = ∟ := by
    euclid_apply extend_point UV V U as X
    euclid_apply Elements.Book1.proposition_32 W V U X VW UV UW
    euclid_finish
  have : ∠ W:V:U + ∠ T:W:V = ∟ := by
    euclid_apply extend_point WT W T as Y
    euclid_apply Elements.Book1.proposition_32 V W T Y VW WT UV
    euclid_finish
  -- euclid_assert ∠ T:W:V = ∠ V:U:W
  euclid_finish

end UniGeo.Similarity

-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle T V W UV VW WT ∧
-- formTriangle T U W UV UW WT ∧
-- To:
-- formTriangle V W U VW UW UV ∧
-- distinctPointsOnLine W T WT ∧
-- twoLinesIntersectAtPoint WT UV T ∧
