import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- triple_incidence_2 CK AC BC c k a b: consumes b.sameSide a CK + ¬k.sameSide b AC ⟹ k.sameSide a BC.
theorem helper_1_47_step17_ss_kBC
    (a b c k : Point) (CK AC BC : Line)
    (hc_CK : c.onLine CK) (hc_AC : c.onLine AC) (hc_BC : c.onLine BC)
    (hk_CK : k.onLine CK) (ha_AC : a.onLine AC) (hb_BC : b.onLine BC)
    (hck : c ≠ k)
    (h_b_nAC : ¬b.onLine AC)
    (h_nk_same_b_AC : ¬k.sameSide b AC)
    (h_bSameA_CK : b.sameSide a CK) :
    k.sameSide a BC := by
  euclid_apply (triple_incidence_2 CK AC BC c k a b)
  euclid_finish

end Elements.Book1
