import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_sas_tri2
    (a b c k : Point) (BC BK CK : Line)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hb_BK : b.onLine BK) (hk_BK : k.onLine BK)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK)
    (hck_len : |(c─k)| = |(a─c)|)
    (h_k_nBC : ¬k.onLine BC) (hcb : c ≠ b) (hca : c ≠ a) :
    formTriangle c b k BC BK CK := by
  euclid_finish

end Elements.Book1
