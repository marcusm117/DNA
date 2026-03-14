import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_3 : ∀ (O P N Q G H : Point) (OP NQ ON PQ OG PH GH NG: Line),
  formConvexQuadrilateral O P N Q OP NQ ON PQ ∧
  formConvexQuadrilateral O G P H OG PH OP GH ∧
  between N O G ∧
  N.onLine NG ∧ O.onLine NG ∧ G.onLine NG ∧
  ∠ N:O:P = ∟ ∧
  ¬ OP.intersectsLine NQ ∧
  ∠ Q:N:P = ∠ P:G:O →
  (△ P:G:O).similar (△ N:P:O) :=
by sorry

end UniGeo.Additional
