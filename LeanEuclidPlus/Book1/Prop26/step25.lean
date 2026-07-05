import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step25
    (a b c e f h : Point) (AH : Line)
    (hbetween : between b h c)
    (hlen : |(b─h)| = |(e─f)|)
    (ha_AH : a.onLine AH)
    (hh_AH : h.onLine AH) :
    between b h c ∧ |(b─h)| = |(e─f)| ∧ a.onLine AH ∧ h.onLine AH :=
  ⟨hbetween, hlen, ha_AH, hh_AH⟩

end Elements.Book1
