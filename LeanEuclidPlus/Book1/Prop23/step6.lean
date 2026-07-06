import SystemE
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_23_step6
    (c d e a f g : Point) (CD CE DE FA FG AB : Line)
    (hd_CD : d.onLine CD) (hc_CD : c.onLine CD) (hdc : d ≠ c)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hd_notCE : ¬d.onLine CE)
    (hstep2 : formTriangle a f g FA FG AB)
    (hstep3 : |(c─d)| = |(a─f)|)
    (hstep4 : |(c─e)| = |(a─g)|)
    (hstep5 : |(d─e)| = |(f─g)|)
    (hassump1 : |(c─d)| = |(a─f)| ∧ |(c─e)| = |(a─g)|)
    (hassump2 : |(d─e)| = |(f─g)|)
    : ∠ d:c:e = ∠ f:a:g := by
  euclid_apply (proposition_8 c d e a f g CD DE CE FA FG AB)
  assumption

end Elements.Book1
