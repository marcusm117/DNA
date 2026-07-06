import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The square HC on AC: a,c on AC; h,k on HK (AC ∥ HK); a,h on AH; c,k on CK (AH ∥ CK).
theorem helper_1_47_step20_hcpgram
    (a c h k : Point) (AC HK AH CK : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (ha_AH : a.onLine AH) (hh_AH : h.onLine AH)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK) (hkc : k ≠ c)
    (h_h_same_a_CK : h.sameSide a CK)
    (h_nHKAC : ¬HK.intersectsLine AC) (h_nAHCK : ¬AH.intersectsLine CK) :
    formParallelogram a c h k AC HK AH CK := by
  euclid_finish

end Elements.Book1
