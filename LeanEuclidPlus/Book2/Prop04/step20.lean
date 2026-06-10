import SystemE
import Book.Prop30
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.20: the squares HF and KC are on AC and CB — area(HF) = |AC|², area(KC) = |CB|².
-- Uses helper_2_positions to pin the parallelogram orientations, derives the two missing parallels
-- (HK∥DE, CF∥BE) via [1.30], then rectangle_area on each right-angled square.
set_option systemE.solverTime 30 in
theorem helper_2_step20 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
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
    (hDEAB' : DE ≠ AB) (hBEAD : BE ≠ AD)
    (hstep17 : |(c─g)| = |(c─b)|) (hstep19 : |(h─g)| = |(a─c)|)
    (hstep18 : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
               (∠ d:h:g = ∟ ∧ ∠ h:g:f = ∟ ∧ ∠ g:f:d = ∟ ∧ ∠ f:d:h = ∟))
    (hcgk : ∠ c:g:k = ∟) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
    (Triangle.area △ c:b:k + Triangle.area △ c:k:g = |(c─b)| * |(c─b)|) := by
  euclid_intros
  euclid_apply (helper_2_positions a b c d e f g h k AB DE AD BE CF HK BD)
  euclid_apply (proposition_30 HK DE AB)
  euclid_apply (proposition_30 CF BE AD)
  euclid_assert |(h─d)| = |(a─c)|
  euclid_apply (rectangle_area h g d f HK DE AD CF)
  euclid_apply (rectangle_area c b g k AB HK CF BE)
  euclid_finish

end Elements.Book2
