import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_2_step6 (b c g : Point) (CGH : Circle)
    (hbc : b.isCentre CGH) (hcc : c.onCircle CGH) (hgc : g.onCircle CGH) :
    |(b─c)| = |(b─g)| := by
  euclid_apply (point_on_circle_onlyif b c g CGH)
  euclid_finish

end Elements.Book1
