import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_5 : ∀ (P Q R S T U : Point) (PR RU PU PQ TQ PT : Line),
  formTriangle P R U PR RU PU ∧
  formTriangle P Q T PQ TQ PT ∧
  twoLinesIntersectAtPoint RU TQ S ∧
  between P Q R ∧
  between P U T ∧
  ∠ P:R:U = ∠ P:T:Q ∧
  |(Q─T)| = |(R─U)| →
  (△ P:R:U).congruent (△ P:T:Q) :=
by
  euclid_intros
  euclid_assert ∠ U:P:R = ∠ Q:P:T
  euclid_finish

end UniGeo.Congruent


-- Changed the following clauses for a more faithful formalization of the clean text and diagram:
-- formTriangle P R U PR RU PT ∧
-- formTriangle P Q T PR TQ PT ∧
-- twoLinesIntersectAtPoint TQ RU S ∧
-- To:
-- formTriangle P R U PR RU PU ∧
-- formTriangle P Q T PQ TQ PT ∧
-- twoLinesIntersectAtPoint RU TQ S ∧
