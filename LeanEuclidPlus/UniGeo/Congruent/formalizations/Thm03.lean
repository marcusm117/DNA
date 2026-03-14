import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_3 : ∀ (P Q R S T : Point) (SP TS PT RS TR : Line),
  formTriangle R S T RS TS TR ∧
  formTriangle P S T SP TS PT ∧
  twoLinesIntersectAtPoint TR SP Q ∧
  ∠ S:P:T = ∠ T:R:S ∧
  ∠ R:S:T = ∟ ∧
  ∠ P:T:S = ∟ →
  (△ R:S:T).congruent (△ P:T:S) :=
by
  euclid_intros
  euclid_assert ∠ P:T:S = ∠ R:S:T
  euclid_finish

end UniGeo.Congruent


-- Removed the following redundant clauses for a more faithful formalization of the clean text and diagram:
-- P.sameSide R ST
