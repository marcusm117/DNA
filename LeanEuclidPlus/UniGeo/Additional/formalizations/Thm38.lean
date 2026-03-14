import SystemE
import UniGeo.Relations
namespace UniGeo.Additional
theorem theorem_8 : ∀ (J K L W V U : Point) (JK KL LJ UV VW UW : Line),
  formTriangle J K L JK KL LJ ∧
  |(J─K)| = |(J─L)| ∧
  distinctPointsOnLine U V UV ∧
  between J U K ∧
  between J V L ∧
  between K W L ∧
  distinctPointsOnLine W V VW ∧
  distinctPointsOnLine U W UW ∧
  ¬ UV.intersectsLine KL →
  formTriangle U V W UV VW UW ∧
  |(W─U)| = |(W─V)| :=
by sorry
end UniGeo.Additional
