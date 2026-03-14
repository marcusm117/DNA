import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_5 : ∀ (U V W X Y Z M : Point) (UV VW WU UX VY WZ : Line),
  formTriangle U V W UV VW WU ∧
  distinctPointsOnLine U X UX ∧ between V X W ∧
  distinctPointsOnLine V Y VY ∧ between U Y W ∧
  distinctPointsOnLine W Z WZ ∧ between U Z V ∧
  twoLinesIntersectAtPoint UX VW X ∧
  twoLinesIntersectAtPoint VY WU Y ∧
  twoLinesIntersectAtPoint WZ UV Z ∧
  twoLinesIntersectAtPoint UX WZ M ∧
  twoLinesIntersectAtPoint WZ VY M ∧
  ∠ U:X:V = ∟ ∧
  ∠ V:Y:W = ∟ ∧
  ∠ W:Z:U = ∟ ∧
  |(M─X)| = |(M─Y)| ∧
  |(M─Y)| = |(M─Z)| →
  |(U─V)| = |(V─W)| ∧
  |(V─W)| = |(W─U)| :=
by sorry

end UniGeo.Additional
