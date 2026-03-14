import SystemE
import UniGeo.Relations
namespace UniGeo.Additional
theorem theorem_8 : ∀ (S T U F E D : Point) (ST TU US DE EF DF : Line),
  formTriangle S T U ST TU US ∧
  |(S─T)| = |(S─U)| ∧
  distinctPointsOnLine D E DE ∧
  between S D T ∧
  between S E U ∧
  between T F U ∧
  distinctPointsOnLine F E EF ∧
  distinctPointsOnLine D F DF ∧
  ¬ DE.intersectsLine TU →
  formTriangle D E F DE EF DF ∧
  |(F─D)| = |(F─E)| :=
by sorry
end UniGeo.Additional
