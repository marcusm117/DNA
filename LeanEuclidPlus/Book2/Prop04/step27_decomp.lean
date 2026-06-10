import SystemE
import Book.Prop30

namespace Elements.Book2

open Elements.Book1

-- 2.4.27 (sub): the four sub-figures HF, CK, AG, GE tile the square ADEB.
-- The big square ADEB is cut by the vertical CF and the horizontal HK into the four sub-figures.
-- Area additivity: sum of the four = area of ADEB (= △d:a:b + △d:b:e). Positions gives the
-- betweenness facts; CF∥BE derived via [1.30].
set_option systemE.solverTime 30 in
theorem helper_2_step27_decomp (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
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
    (hHKDE : HK ≠ DE) (hABHKne : AB ≠ HK) (hCFBE : CF ≠ BE) (hADCFne : AD ≠ CF) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
    (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
    (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
    (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
    Triangle.area △ d:a:b + Triangle.area △ d:b:e := by
  euclid_intros
  euclid_apply (helper_2_positions a b c d e f g h k AB DE AD BE CF HK BD)
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (proposition_30 HK DE AB)
  -- split ADEB by CF (f on DE, c on AB) into left strip ACFD + right strip CBEF
  euclid_apply (sum_parallelograms_area d e a b f c DE AB AD BE)
  -- split left strip (a,d on AD; c,f on CF; AD ∥ CF) by HK at h (on AD) and g (on CF)
  euclid_apply (sum_parallelograms_area a c f d h g AB CF AD DE)
  -- split right strip (c,b on AB; f,e on DE) by HK at g and k
  euclid_apply (sum_parallelograms_area c b e f g k AB DE CF BE)
  euclid_finish

end Elements.Book2
