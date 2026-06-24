import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step5 (2.9.5): FG is the line through F parallel to AB (proposition_31's outputs).
theorem helper_2_9_step5
  (f : Point) (FG AB : Line)
  (h1 : f.onLine FG) (h2 : ¬FG.intersectsLine AB) :
  f.onLine FG ∧ ¬(FG.intersectsLine AB) := by
  euclid_finish

end Elements.Book2
