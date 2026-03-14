import SystemE
import UniGeo.Relations
namespace UniGeo.Additional
theorem theorem_8 : ∀ (X Y Z K J I : Point) (XY YZ ZX IJ JK IK : Line),
  formTriangle X Y Z XY YZ ZX ∧
  |(X─Y)| = |(X─Z)| ∧
  distinctPointsOnLine I J IJ ∧
  between X I Y ∧
  between X J Z ∧
  between Y K Z ∧
  distinctPointsOnLine K J JK ∧
  distinctPointsOnLine I K IK ∧
  ¬ IJ.intersectsLine YZ →
  formTriangle I J K IJ JK IK ∧
  |(K─I)| = |(K─J)| :=
by sorry
end UniGeo.Additional
