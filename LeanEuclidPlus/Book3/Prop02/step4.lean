import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step4 (d f p : Point) (ABC : Circle) (DFE : Line)
    (hd : d.isCentre ABC) (hfABC : f.onCircle ABC) (hfDFE : f.onLine DFE)
    (hbet : between d f p) :
    f.onCircle ABC ∧ between d f p := by
  exact ⟨hfABC, hbet⟩

end Elements.Book3
