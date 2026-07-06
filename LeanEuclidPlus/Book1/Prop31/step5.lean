import SystemE
import Book1.Prop27.Main
import Book1.Prop31.step5_opp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

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
  have step5_opp : e.opposingSides c AD := by euclid_apply (helper_1_31_step5_opp a b c d e EF BC AD (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show a.onLine EF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show between b d c; assumption)) (by euclid_assumption "" (show e.onLine AD ∨ e.sameSide b AD; assumption)) (by euclid_assumption "" (show ∠ e:a:d = ∠ a:d:c; assumption)))
  euclid_apply (proposition_27 e c a d EF BC AD)
  euclid_finish

end Elements.Book1
