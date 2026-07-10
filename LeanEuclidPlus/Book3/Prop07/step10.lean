import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop07.step10_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step10
    (ABCD : Circle) (a d e f g : Point) (AD GE : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hg : g.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    (h_gne_a : g ≠ a) (h_gne_d : g ≠ d)
    (hassump1 : |(g─f)| + |(f─e)| > |(g─e)|)
    (hassump2 : |(e─g)| = |(e─d)|)
    : |(g─f)| + |(f─e)| > |(e─d)| := by
  have step10_assumption1 : |(g─f)| + |(f─e)| > |(g─e)| := by euclid_apply (helper_3_7_step10_assumption1 ABCD a d e f g AD GE (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show a.onCircle ABCD; assumption)) (by euclid_assumption "" (show d.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "" (show between e f d; assumption)) (by euclid_assumption "" (show g.onLine GE; assumption)) (by euclid_assumption "" (show e.onLine GE; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g ≠ d; assumption)))
  linarith [segment_symmetric g e]

end Elements.Book3
