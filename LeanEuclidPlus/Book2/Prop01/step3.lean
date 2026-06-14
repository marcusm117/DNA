import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.3: GH drawn through G parallel to BC [Prop.~1.31]. The incidence g.onLine GH and the
   parallelism ¬GH.intersectsLine BC are produced by the proposition_31 construction in Main;
   this helper repackages them. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step3 (g : Point) (GH BC : Line)
    (hgGH : g.onLine GH) (hpar : ¬(GH.intersectsLine BC)) :
    g.onLine GH ∧ ¬(GH.intersectsLine BC) := by
  exact ⟨hgGH, hpar⟩

end Elements.Book2
