import SystemE
import UniGeo.Relations

namespace UniGeo.Congruent

theorem theorem_8 : ∀ (P Q R S T : Point) (PQ QR RS ST PT PS SQ : Line),
  formTriangle P S T PS ST PT ∧
  formTriangle P Q S PQ SQ PS ∧
  formTriangle Q R S QR RS SQ ∧
  P.opposingSides R SQ ∧
  Q.opposingSides T PS ∧
  ∠ R:Q:S = ∠ S:P:T ∧
  |(P─T)| = |(Q─R)| ∧
  |(P─Q)| = |(Q─S)| ∧
  |(Q─S)| = |(S─P)| →
  (△ P:S:T).congruent (△ Q:S:R) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Congruent


-- Removed the following wrong clauses:
-- Q.sameSide R PS ∧
-- P.sameSide T QS ∧
