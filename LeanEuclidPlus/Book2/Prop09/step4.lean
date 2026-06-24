import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step4 (2.9.4): DF is the line through D parallel to EC (proposition_31's outputs).
theorem helper_2_9_step4
  (d : Point) (DF CE : Line)
  (h1 : d.onLine DF) (h2 : ¬DF.intersectsLine CE) :
  d.onLine DF ∧ ¬(DF.intersectsLine CE) := by
  euclid_finish

end Elements.Book2
