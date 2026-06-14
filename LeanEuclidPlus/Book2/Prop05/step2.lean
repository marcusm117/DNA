import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.2: BE joined. line_from_points b e in Main puts b, e on BE; b ≠ e because e lies strictly to
   one side of BF (e.sameSide c BF) while b is on BF, so e is off BF and hence e ≠ b. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step2 (b c e : Point) (BE BF : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hbBF : b.onLine BF) (hecBF : e.sameSide c BF) :
    distinctPointsOnLine b e BE := by
  euclid_finish

end Elements.Book2
