import SystemE
import Book.Prop27
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_31_step5
    (a b c d e : Point) (EF BC AD : Line)
    (heEF : e.onLine EF) (haEF : a.onLine EF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hdBC : d.onLine BC) (hcBC : c.onLine BC)
    (hbBC : b.onLine BC) (haoff : ¬a.onLine BC)
    (hane : e ≠ a) (had : a ≠ d)
    (hbdc : between b d c)
    (heon_or : e.onLine AD ∨ e.sameSide b AD)
    (hassump1 : ∠ e:a:d = ∠ a:d:c)
    : ¬(EF.intersectsLine BC) := by
  have hea : distinctPointsOnLine e a EF := ⟨heEF, haEF, hane⟩
  have hdc : distinctPointsOnLine d c BC := ⟨hdBC, hcBC, by euclid_finish⟩
  have hadAD : distinctPointsOnLine a d AD := ⟨haAD, hdAD, had⟩
  have step5_opp : e.opposingSides c AD := by sorry
  euclid_apply (proposition_27 e c a d EF BC AD)
  euclid_finish

end Elements.Book1
