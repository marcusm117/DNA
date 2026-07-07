import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- False: FE⊥AC and FE⊥BD at the same point e, with both lines through e,
-- forces AC=BD by perpendicular uniqueness, contradicting AC≠BD.
theorem helper_3_4_step10
    (a b c d e f : Point) (AC BD FE : Line) (ABCD : Circle)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (hnfAC : ¬f.onLine AC) (hnfBD : ¬f.onLine BD)
    (hstep4 : distinctPointsOnLine f e FE)
    (hbetac : between a e c) (hbetbd : between b e d)
    (hACBD : AC ≠ BD)
    (hstep5 : ∠ f:e:a = ∟)
    (hstep7 : ∠ f:e:b = ∟) :
    False := by
  euclid_finish

end Elements.Book3
