import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step8
  (a b c d : Point) (ABC : Circle)
  (hd_on : d.onCircle ABC) (hdb : b ≠ d) (hdc : c ≠ d) (hda : a ≠ d)
  : d.onCircle ABC ∧ b ≠ d ∧ c ≠ d ∧ a ≠ d :=
  ⟨hd_on, hdb, hdc, hda⟩

end Elements.Book3
