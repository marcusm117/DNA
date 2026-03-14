import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Congruent

theorem theorem_1 : ∀ (U V X W Y : Point) (UV VX XU VW WY YV UW : Line),
  formTriangle U V X UV VX XU ∧
  formTriangle V W Y VW WY YV ∧
  (distinctPointsOnLine U W UW ∧ distinctPointsOnLine V W UW ∧ distinctPointsOnLine V U UW) ∧
  (X.sameSide Y UW ∧ X ≠ Y) ∧
  |(W─Y)| = |(V─X)| ∧
  |(V─Y)| = |(U─X)| ∧
  (between U V W ∧ |(U─V)| = |(V─W)|) →
  (△ V:W:Y).congruent (△ U:V:X) :=
by
  euclid_intros
  euclid_finish

end UniGeo.Congruent