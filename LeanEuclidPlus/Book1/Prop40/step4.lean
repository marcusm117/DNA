import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_40_step4 (a d f e : Point) (FE AF BC : Line)
    (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (hfAF : f.onLine AF) (haAF : a.onLine AF)
    (heBC : e.onLine BC) (haside : a.sameSide d BC)
    (hnAF : ¬AF.intersectsLine BC) :
    distinctPointsOnLine f e FE := by
  refine ⟨hfFE, heFE, ?_⟩
  intro hfe
  have haBC : ¬a.onLine BC := same_side_not_on_line a d BC haside
  have hAFBC : AF ≠ BC := fun h => haBC (h ▸ haAF)
  exact hnAF (intersection_lines_common_point e AF BC ⟨hfe ▸ hfAF, heBC, hAFBC⟩)

end Elements.Book1
