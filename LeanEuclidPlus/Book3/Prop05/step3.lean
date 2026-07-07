import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_5_step3 (ABC CDG : Circle) (EFG : Line) (e f g : Point)
    (heEFG : e.onLine EFG) (hfABC : f.onCircle ABC) (hfEFG : f.onLine EFG)
    (hgCDG : g.onCircle CDG) (hgEFG : g.onLine EFG)
    : e.onLine EFG ∧ f.onCircle ABC ∧ f.onLine EFG ∧ g.onCircle CDG ∧ g.onLine EFG := by
  exact ⟨heEFG, hfABC, hfEFG, hgCDG, hgEFG⟩

end Elements.Book3
