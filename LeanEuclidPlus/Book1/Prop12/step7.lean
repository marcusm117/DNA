import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step7 (c e g : Point) (EFG : Circle)
    (hcen : c.isCentre EFG) (heEFG : e.onCircle EFG) (hgEFG : g.onCircle EFG) :
    |(c─g)| = |(c─e)| := by
  euclid_finish

end Elements.Book1
