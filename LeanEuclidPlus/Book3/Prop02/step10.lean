import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step10 (b d f : Point) (ABC : Circle)
    (hb : b.onCircle ABC) (hf : f.onCircle ABC) (hd : d.isCentre ABC) :
    |(d─b)| = |(d─f)| := by
  euclid_finish

end Elements.Book3
