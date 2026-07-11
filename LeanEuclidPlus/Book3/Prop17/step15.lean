import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step15 (a d e f : Point) (AE : Line)
    (ha_onAE : a.onLine AE) (he_onAE : e.onLine AE) (hd_onAE : d.onLine AE)
    (hf_notAE : ¬f.onLine AE)
    (hbetween_ade : between a d e)
    (h_angle : ∠ a:d:f = ∟) :
    ∠ e:d:f = ∟ := by
  euclid_finish

end Elements.Book3
