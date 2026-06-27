import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step5 (2.10.5): FD is the line through D parallel to CE (proposition_31's outputs).
theorem helper_2_10_step5
  (d : Point) (FD CE : Line)
  (h1 : d.onLine FD) (h2 : ¬FD.intersectsLine CE) :
  d.onLine FD ∧ ¬(FD.intersectsLine CE) := by
  euclid_finish

end Elements.Book2
