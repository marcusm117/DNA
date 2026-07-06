import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_sas_tri1
    (a b c e : Point) (CE AE AC : Line)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (ha_AE : a.onLine AE) (he_AE : e.onLine AE)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hce_len : |(c─e)| = |(b─c)|)
    (h_a_nCE : ¬a.onLine CE) (hcb : c ≠ b) (hca : c ≠ a) :
    formTriangle c e a CE AE AC := by
  euclid_finish

end Elements.Book1
