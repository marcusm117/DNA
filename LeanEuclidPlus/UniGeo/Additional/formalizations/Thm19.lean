import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_9 : ∀ (U V W X F G : Point) (f g : Circle) (UV FX GW : Line),
  U.isCentre f ∧
  V.isCentre g ∧
  distinctPointsOnLine U V UV ∧
  UV.intersectsCircle f ∧ W.onLine UV ∧ W.onCircle f ∧
  UV.intersectsCircle g ∧ X.onLine UV ∧ X.onCircle g ∧
  f.intersectsCircle g ∧
  F.onCircle f ∧ F.onCircle g ∧
  G.onCircle f ∧ G.onCircle g ∧
  F.opposingSides G UV ∧
  distinctPointsOnLine F X FX ∧
  distinctPointsOnLine G W GW ∧
  ¬ FX.intersectsLine GW ∧
  ∠ V:F:X = ∠ U:G:W →
  (△ V:X:F).similar (△ W:U:G) :=
by sorry

end UniGeo.Additional
