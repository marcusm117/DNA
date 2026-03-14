import SystemE
import UniGeo.Relations

namespace UniGeo.Triangle

theorem theorem_7 : ∀ (T W Y U V X : Point) (TW WY YT UV VX XU : Line),
  formTriangle U V X UV VX XU ∧
  formTriangle T W Y TW WY YT ∧
  ∠ W:T:Y = ∠ U:V:X ∧
  |(T─Y)| / |(U─V)| = |(T─W)| / |(V─X)| →
  ∠ T:W:Y = ∠ U:X:V :=
by
  euclid_intros
  euclid_finish

end UniGeo.Triangle
