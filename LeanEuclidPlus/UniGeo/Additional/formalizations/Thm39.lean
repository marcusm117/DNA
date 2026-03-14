import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_9 : ∀ (G H I J R S : Point) (r s : Circle) (GH RJ SI : Line),
  G.isCentre r ∧
  H.isCentre s ∧
  distinctPointsOnLine G H GH ∧
  GH.intersectsCircle r ∧ I.onLine GH ∧ I.onCircle r ∧
  GH.intersectsCircle s ∧ J.onLine GH ∧ J.onCircle s ∧
  r.intersectsCircle s ∧
  R.onCircle r ∧ R.onCircle s ∧
  S.onCircle r ∧ S.onCircle s ∧
  R.opposingSides S GH ∧
  distinctPointsOnLine R J RJ ∧
  distinctPointsOnLine S I SI ∧
  ¬ RJ.intersectsLine SI ∧
  ∠ H:R:J = ∠ G:S:I →
  (△ H:J:R).similar (△ I:G:S) :=
by sorry

end UniGeo.Additional
