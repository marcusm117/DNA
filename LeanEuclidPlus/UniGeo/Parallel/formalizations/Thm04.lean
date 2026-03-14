import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Parallel

theorem theorem_4 : ∀ (S U V X R Y T W : Point) (SU VX RY : Line),
  distinctPointsOnLine S U SU ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine R Y RY ∧
  twoLinesIntersectAtPoint SU RY T ∧ between S T U ∧ between T W Y ∧
  twoLinesIntersectAtPoint VX RY W ∧ between V W X ∧ between R T W ∧
  V.sameSide S RY ∧ V ≠ S ∧
  X.sameSide U RY ∧ X ≠ U ∧
  ¬ VX.intersectsLine SU →
  ∠ S:T:W = ∠ T:W:X :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29 X V U S Y R W T VX SU RY
  euclid_finish

end UniGeo.Parallel


-- Added the following clauses for a more faithful formalization of the clean text and diagram:
--  V ≠ S
--  X ≠ U
