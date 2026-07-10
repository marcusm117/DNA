import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |MK| = |ML|: both k and l are on circle ABC with centre m.
set_option systemE.solverTime 30 in
theorem helper_3_8_step16
    (ABC : Circle) (m k l : Point)
    (hm : m.isCentre ABC) (hk : k.onCircle ABC) (hl : l.onCircle ABC) :
    |(m─k)| = |(m─l)| := by
  exact (point_on_circle_onlyif m k l ABC ⟨hm, hk, hl⟩).symm

end Elements.Book3
