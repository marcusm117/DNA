import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_4_step4 (a c f e : Point) (ABCD : Circle) (AC FE : Line)
    (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hnfAC : ¬f.onLine AC)
    (hbet : between a e c) :
    distinctPointsOnLine f e FE := by
  have hne : f ≠ e := by euclid_finish
  exact ⟨hfFE, heFE, hne⟩

end Elements.Book3
