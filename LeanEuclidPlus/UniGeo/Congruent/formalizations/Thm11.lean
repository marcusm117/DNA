import SystemE
import Book.Prop29
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_11 : ∀ (T U V W : Point) (TU UV VW TW TV : Line),
  formConvexQuadrilateral T U W V TU VW TW UV ∧
  distinctPointsOnLine T V TV ∧
  |(T─U)| = |(V─W)| ∧
  ¬ TU.intersectsLine VW →
  (△ T:U:V).congruent (△ V:W:T) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' U W T V TU VW TV
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle T U V TU UV TV ∧
-- formTriangle T V W TV VW TW ∧
-- U.opposingSides W TV ∧
-- To:
-- formConvexQuadrilateral T U W V TU VW TW UV ∧
-- distinctPointsOnLine T V TV ∧
