import SystemE
import UniGeo.Relations

namespace UniGeo.Additional

theorem theorem_3 : ∀ (C D B E U V : Point) (CD BE CB DE CU DV UV BU: Line),
  formConvexQuadrilateral C D B E CD BE CB DE ∧
  formConvexQuadrilateral C U D V CU DV CD UV ∧
  between B C U ∧
  B.onLine BU ∧ C.onLine BU ∧ U.onLine BU ∧
  ∠ B:C:D = ∟ ∧
  ¬ CD.intersectsLine BE ∧
  ∠ E:B:D = ∠ D:U:C →
  (△ D:U:C).similar (△ B:D:C) :=
by sorry

end UniGeo.Additional
