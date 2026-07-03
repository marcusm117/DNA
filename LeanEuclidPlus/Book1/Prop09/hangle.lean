import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_9_hangle (a b c d e f : Point) (AB AC AF : Line)
    (ha_on_AB : a.onLine AB) (hb_on_AB : b.onLine AB) (hd_on_AB : d.onLine AB)
    (ha_on_AC : a.onLine AC) (hc_on_AC : c.onLine AC)
    (ha_on_AF : a.onLine AF) (hf_on_AF : f.onLine AF)
    (hbtw_adb : between a d b) (hbtw_aec : between a e c)
    (hba : b ≠ a) (hca : a ≠ c) (hfa : f ≠ a)
    (step9 : ∠ d:a:f = ∠ e:a:f) :
    ∠ b:a:f = ∠ c:a:f := by
  euclid_apply (equal_angles a d b f f AB AF)
  euclid_apply (equal_angles a e c f f AC AF)
  euclid_finish

end Elements.Book1
