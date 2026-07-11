import SystemE
import Book1.Prop20.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Triangle inequality ME + EN > MN (Prop.~1.20).
-- Key: must establish formTriangle e m n ME MN EN, which requires ¬e.onLine MN.
-- ¬e.onLine MN: e and l are both on EK, e ≠ l (from between e l k),
--   so if e were on MN then EK = MN, but m0 is on MN yet off EK — contradiction.
theorem helper_3_15_step8
    (m e n l m0 k : Point) (ABCD : Circle) (ME MN EN EK : Line)
    (h_centre : e.isCentre ABCD)
    (hm_on : m.onCircle ABCD) (hn_on : n.onCircle ABCD)
    (hm_ME : m.onLine ME) (he_ME : e.onLine ME)
    (hm_MN : m.onLine MN) (hn_MN : n.onLine MN) (hl_MN : l.onLine MN)
    (he_EN : e.onLine EN) (hn_EN : n.onLine EN)
    (he_EK : e.onLine EK) (hk_EK : k.onLine EK)
    (hbetw_mln : between m l n)
    (hbetw_elk : between e l k)
    (hm0_MN : m0.onLine MN) (hm0_off : ¬m0.onLine EK) :
    |(m─e)| + |(e─n)| > |(m─n)| := by
  have hel : e ≠ l := (between_symm e l k hbetw_elk).2.1
  have hmn : m ≠ n := (between_symm m l n hbetw_mln).2.2.1
  have hme : m ≠ e := by euclid_finish
  have hen : e ≠ n := by euclid_finish
  have he_off_MN : ¬e.onLine MN := by euclid_finish
  have htri : formTriangle e m n ME MN EN := by euclid_finish
  euclid_apply (Elements.Book1.proposition_20 e m n ME MN EN)
  linarith [segment_symmetric m e, segment_symmetric e n]

end Elements.Book3
