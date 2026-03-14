import SystemE
import UniGeo.Relations
namespace UniGeo.Additional
theorem theorem_8 : ∀ (B C D O N M : Point) (BC CD DB MN NO MO : Line),
  formTriangle B C D BC CD DB ∧
  |(B─C)| = |(B─D)| ∧
  distinctPointsOnLine M N MN ∧
  between B M C ∧
  between B N D ∧
  between C O D ∧
  distinctPointsOnLine O N NO ∧
  distinctPointsOnLine M O MO ∧
  ¬ MN.intersectsLine CD →
  formTriangle M N O MN NO MO ∧
  |(O─M)| = |(O─N)| :=
by sorry
end UniGeo.Additional
