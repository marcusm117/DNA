import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_3_step3 (a d e : Point) (DEF : Circle)
    (hc : a.isCentre DEF) (hd : d.onCircle DEF) (he : e.onCircle DEF) :
    |(a─e)| = |(a─d)| := by
  exact point_on_circle_onlyif a d e DEF ⟨hc, hd, he⟩

end Elements.Book1
