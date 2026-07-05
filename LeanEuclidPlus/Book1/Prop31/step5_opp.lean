import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_31_step5_opp
    (a b c d e : Point) (EF BC AD : Line)
    (heEF : e.onLine EF) (haEF : a.onLine EF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hdBC : d.onLine BC) (hcBC : c.onLine BC)
    (haoff : ¬a.onLine BC) (had : a ≠ d) (hane : e ≠ a)
    (hbdc : between b d c)
    (heon_or : e.onLine AD ∨ e.sameSide b AD)
    (hassump1 : ∠ e:a:d = ∠ a:d:c)
    : e.opposingSides c AD := by
  euclid_finish

end Elements.Book1
