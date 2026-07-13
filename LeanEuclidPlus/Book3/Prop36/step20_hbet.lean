import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step20_hbet (a c f : Point) (DA : Line)
    (ha_DA : a.onLine DA) (hc_DA : c.onLine DA) (hf_DA : f.onLine DA)
    (hlen : |(a─f)| = |(f─c)|) (hac : a ≠ c) (haf : a ≠ f) (hcf : c ≠ f) :
    between a f c := by euclid_finish

end Elements.Book3
