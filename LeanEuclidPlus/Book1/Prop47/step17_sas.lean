import SystemE
import Book.Prop04
import Book1.Prop47.step17_sas_tri1
import Book1.Prop47.step17_sas_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- SAS △CEA ≅ △CBK: |CE|=|CB|, |CA|=|CK|, ∠ECA=∠BCK ⟹ △ACE = △CBK (mirror of step11/12).
theorem helper_1_47_step17_sas
    (a b c e k : Point) (CE AE AC BC BK CK : Line)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (ha_AE : a.onLine AE) (he_AE : e.onLine AE)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hb_BK : b.onLine BK) (hk_BK : k.onLine BK)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK)
    (hce_len : |(c─e)| = |(b─c)|) (hck_len : |(c─k)| = |(a─c)|)
    (h_eca_bck : ∠ e:c:a = ∠ b:c:k)
    (h_a_nCE : ¬a.onLine CE) (h_k_nBC : ¬k.onLine BC)
    (hcb : c ≠ b) (hca : c ≠ a) :
    Triangle.area △ a:c:e = Triangle.area △ c:b:k := by
  have step17_sas_tri1 : formTriangle c e a CE AE AC := by euclid_apply (helper_1_47_step17_sas_tri1 a b c e CE AE AC (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show |(c─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)))
  have step17_sas_tri2 : formTriangle c b k BC BK CK := by euclid_apply (helper_1_47_step17_sas_tri2 a b c k BC BK CK (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine BK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show |(c─k)| = |(a─c)|; assumption)) (by euclid_assumption "" (show ¬k.onLine BC; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)))
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_finish

end Elements.Book1
