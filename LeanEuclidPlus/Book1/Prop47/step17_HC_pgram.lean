import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The square HAKC on AC (mirror of step14_pgram): h,a on AH; k,c on CK (AH ∥ CK); h,k on HK; a,c on AC (HK ∥ AC).
theorem helper_1_47_step17_HC_pgram
    (a c h k : Point) (AH CK HK AC : Line)
    (hh_AH : h.onLine AH) (ha_AH : a.onLine AH)
    (hk_CK : k.onLine CK) (hc_CK : c.onLine CK)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c)
    (hh_nAC : ¬h.onLine AC)
    (h_nAHCK : ¬AH.intersectsLine CK) (h_nHKAC : ¬HK.intersectsLine AC) :
    formParallelogram h a k c AH CK HK AC := by
  have hk_nAC : ¬k.onLine AC := by
    intro hk_AC
    euclid_apply (intersection_lines_common_point k HK AC)
    euclid_finish
  have hhk_AC : h.sameSide k AC := by
    by_contra hcon
    euclid_apply (intersection_lines_opposing h k AC HK)
    euclid_finish
  euclid_finish

end Elements.Book1
