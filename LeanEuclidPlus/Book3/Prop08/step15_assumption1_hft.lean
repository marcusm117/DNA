import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_8_step15_assumption1_hft (m l d : Point)
    (ML LD AG : Line)
    (hmAG : m.onLine AG) (hdAG : d.onLine AG)
    (hMLm : m.onLine ML) (hMLl : l.onLine ML)
    (hLDl : l.onLine LD) (hLDd : d.onLine LD)
    (hne_lm : l ≠ m) (hne_ld : l ≠ d) (hne_dm : m ≠ d)
    (hloffAG : ¬l.onLine AG) :
    formTriangle m l d ML LD AG := by
  euclid_finish

end Elements.Book3
