import SystemE
import Book.Prop15
import UniGeo.Relations

namespace UniGeo.Similarity

theorem theorem_11 : ∀ (U V W X Y : Point) (UV VX UX UW WY UY XW VY : Line),
  formTriangle U V X UV VX UX ∧
  formTriangle U W Y UW WY UY ∧
  distinctPointsOnLine X W XW ∧
  distinctPointsOnLine V Y VY ∧
  twoLinesIntersectAtPoint XW VY U ∧
  between W U X ∧
  between V U Y ∧
  |(U─V)| / |(U─W)| = |(U─X)| / |(U─Y)| →
  (△ U:V:X).similar (△ U:W:Y) :=
by
  euclid_intros
  have h1: |(U─V)| = |(V─U)| := by
    euclid_finish
  have h2: |(W─U)| = |(U─W)| := by
    euclid_finish
  have h3: |(V─U)| / |(W─U)| = |(U─V)| / |(U─W)| := by
    rw [←h1, ←h2]
  have : |(V─U)| / |(W─U)| = |(U─X)| / |(U─Y)| := by
    rw [h3]
    exact right_24
  have : Triangle.area (△ U:V:X) > 0 := by
    euclid_finish
  have : Triangle.area (△ U:W:Y) > 0 := by
    euclid_finish
  have : ∠ V:U:X = (∠ W:U:Y) := by
    euclid_apply Elements.Book1.proposition_15 X W V Y U XW VY
    euclid_finish
  euclid_finish

end UniGeo.Similarity


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle U V X VY VX WX ∧
-- formTriangle U W Y WX WY VY ∧
-- To:
-- formTriangle U V X UV VX UX ∧
-- formTriangle U W Y UW WY UY ∧
-- distinctPointsOnLine X W XW ∧
-- distinctPointsOnLine V Y VY ∧
-- twoLinesIntersectAtPoint XW VY U ∧
