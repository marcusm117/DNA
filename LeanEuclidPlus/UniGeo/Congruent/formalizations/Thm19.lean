import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_19 : ∀ (R S T U : Point) (RS ST RT RU : Line),
  formTriangle R S T RS ST RT ∧
  distinctPointsOnLine R U RU ∧
  between S U T ∧
  |(S─U)| = |(T─U)| ∧
  |(R─S)| = |(R─T)| →
  ∠ R:T:U = ∠ R:S:U :=
by
  euclid_intros
  euclid_assert (△ R:S:U).congruent (△ R:T:U)
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle R S U RS ST RU ∧
-- formTriangle R T U RT ST RU ∧
-- To:
-- formTriangle R S T RS ST RT ∧
-- distinctPointsOnLine R U RU ∧
