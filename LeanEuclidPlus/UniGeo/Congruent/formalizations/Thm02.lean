import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_2 : ∀ (T U V W : Point) (UV TW UT VW VT : Line),
  formConvexQuadrilateral U V T W UV TW UT VW ∧
  distinctPointsOnLine V T VT ∧
  formTriangle U V T UV VT UT ∧
  formTriangle V W T VW TW VT ∧
  |(T─U)| = |(V─W)| ∧
  ¬ UT.intersectsLine VW →
  (△ T:U:V).congruent (△ V:W:T) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' U W T V UT VW VT
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- U.opposingSides W TV ∧
-- To:
-- formConvexQuadrilateral U V T W UV TW UT VW ∧
-- distinctPointsOnLine V T VT ∧
