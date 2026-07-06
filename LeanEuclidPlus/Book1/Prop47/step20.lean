import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop47.step20_gbpgram
import Book1.Prop47.step20_hcpgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The squares GB and HC have areas |BA|² and |AC|² (rectangle_area on each square).
theorem helper_1_47_step20
    (a b c f g h k : Point) (AB AC GF AG BF HK AH CK : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hg_GF : g.onLine GF) (hf_GF : f.onLine GF)
    (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
    (hb_BF : b.onLine BF) (hf_BF : f.onLine BF) (hfb : f ≠ b)
    (h_g_same_a_BF : g.sameSide a BF)
    (h_nGFAB : ¬GF.intersectsLine AB) (h_nAGBF : ¬AG.intersectsLine BF)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (ha_AH : a.onLine AH) (hh_AH : h.onLine AH)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK) (hkc : k ≠ c)
    (h_h_same_a_CK : h.sameSide a CK)
    (h_nHKAC : ¬HK.intersectsLine AC) (h_nAHCK : ¬AH.intersectsLine CK)
    (h_agf : (∠ a:g:f : ℝ) = ∟) (h_ahk : (∠ a:h:k : ℝ) = ∟)
    (hag_len : |(a─g)| = |(a─b)|) (hah_len : |(a─h)| = |(a─c)|) :
    (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|) := by
  have step20_gbpgram : formParallelogram a b g f AB GF AG BF := by euclid_apply (helper_1_47_step20_gbpgram a b g f AB GF AG BF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show g.sameSide a BF; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AG.intersectsLine BF; assumption)))
  have step20_hcpgram : formParallelogram a c h k AC HK AH CK := by euclid_apply (helper_1_47_step20_hcpgram a c h k AC HK AH CK (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show h.sameSide a CK; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine CK; assumption)))
  euclid_apply (rectangle_area a b g f AB GF AG BF)
  euclid_apply (rectangle_area a c h k AC HK AH CK)
  have hab : |(a─b)| = |(b─a)| := by euclid_finish
  refine ⟨?_, ?_⟩
  · have hrect : Triangle.area △ a:g:f + Triangle.area △ a:b:f = |(a─b)| * |(a─g)| := by euclid_finish
    have hperm : Triangle.area △ a:f:b = Triangle.area △ a:b:f := by euclid_finish
    have hprod : |(a─b)| * |(a─g)| = |(b─a)| * |(b─a)| := by rw [hag_len, hab]
    linarith [hrect, hperm, hprod]
  · have hrect : Triangle.area △ a:h:k + Triangle.area △ a:c:k = |(a─c)| * |(a─h)| := by euclid_finish
    have hperm : Triangle.area △ a:k:c = Triangle.area △ a:c:k := by euclid_finish
    have hprod : |(a─c)| * |(a─h)| = |(a─c)| * |(a─c)| := by rw [hah_len]
    linarith [hrect, hperm, hprod]

end Elements.Book1
