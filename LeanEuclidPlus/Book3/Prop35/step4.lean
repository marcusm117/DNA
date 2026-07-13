import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_35_step4 (b c e f : Point) (ABCD : Circle) (FB FC FE : Line)
  (hb : b.onCircle ABCD) (hc : c.onCircle ABCD) (hfc : f.isCentre ABCD) (hcen : ¬e.isCentre ABCD)
  (hfFB : f.onLine FB) (hbFB : b.onLine FB)
  (hfFC : f.onLine FC) (hcFC : c.onLine FC)
  (hfFE : f.onLine FE) (heFE : e.onLine FE)
  : distinctPointsOnLine f b FB ∧ distinctPointsOnLine f c FC ∧ distinctPointsOnLine f e FE := by
  euclid_finish

end Elements.Book3
