import SystemE
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.19: HG = AC  [Prop.~1.34]. AHGC is a parallelogram so opposite sides AC and HG are equal.
-- Needs the positional facts (from helper_2_positions) to pin the parallelogram's orientation;
-- then proposition_34' on AHGC. (Same prop_34' as step18; here we only need |HG| = |AC|.)
set_option systemE.solverTime 30 in
theorem helper_2_step19 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdAD : d.onLine AD) (haAD : a.onLine AD) (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hcAB : c.onLine AB) (hacb : between a c b)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hfCF : f.onLine CF) (hfDE : f.onLine DE)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hgBD : g.onLine BD) (hgCF : g.onLine CF)
    (hgHK : g.onLine HK) (hHKAB : ¬(HK.intersectsLine AB))
    (hhHK : h.onLine HK) (hhAD : h.onLine AD)
    (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hbd : b ≠ d) (hbg : b ≠ g) (hdg : d ≠ g) (hCFBD : CF ≠ BD)
    (hah : a ≠ h) (hdh : d ≠ h) (hADHK : AD ≠ HK)
    (hbk : b ≠ k) (hek : e ≠ k) (hBEHK : BE ≠ HK)
    (hdf : d ≠ f) (hef : e ≠ f) (hDECF : DE ≠ CF)
    (hcg : c ≠ g) (hfg : f ≠ g) (hCFHK : CF ≠ HK)
    (hhg : h ≠ g) (hkg : k ≠ g) (hHKCF : HK ≠ CF)
    (hHKDE : HK ≠ DE) (hABHKne : AB ≠ HK) (hCFBE : CF ≠ BE) (hADCFne : AD ≠ CF)
    (hac : a ≠ c) :
    |(h─g)| = |(a─c)| := by
  euclid_intros
  have positions : between a h d ∧ between b k e ∧ between d f e ∧
      between b g d ∧ between c g f ∧ between h g k := by sorry
  euclid_apply (proposition_34' a c h g AB HK AD CF)
  euclid_finish

end Elements.Book2
