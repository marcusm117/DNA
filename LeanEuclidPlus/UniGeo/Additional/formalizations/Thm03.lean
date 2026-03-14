import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_3 : ∀ (X Y W Z P Q : Point) (XY WZ XW YZ XP YQ PQ WP: Line),
  formConvexQuadrilateral X Y W Z XY WZ XW YZ ∧
  formConvexQuadrilateral X P Y Q XP YQ XY PQ ∧
  between W X P ∧
  W.onLine WP ∧ X.onLine WP ∧ P.onLine WP ∧
  ∠ W:X:Y = ∟ ∧
  ¬ XY.intersectsLine WZ ∧
  ∠ Z:W:Y = ∠ Y:P:X →
  (△ Y:P:X).similar (△ W:Y:X) :=
by sorry

end UniGeo.Additional
