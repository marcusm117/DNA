import SystemE
import Book.Prop30
import Book.Prop43

namespace Elements.Book2

open Elements.Book1

-- 2.4.21: the complements AG and GE of the square ADEB about the diagonal BD are equal  [Prop.~1.43].
-- proposition_43 with big parallelogram ADEB, diagonal BD through G, the two parallelograms about
-- the diagonal being the squares HF (=DFHG) and KC (=GKCB). Mapping of prop43's corners
-- (a b c d e f g h k) ↦ (D A B E H K C F G) and lines (AD BC AB CD AC EF GH) ↦ (DE AB AD BE BD HK CF).
-- Takes only raw facts Main supplies; the inner prop_43 / parallelogram_area discharge the
-- sub-parallelogram preconditions from those.
set_option systemE.solverTime 30 in
theorem helper_2_step21 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
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
    (hDEAB' : DE ≠ AB) (hBEAD : BE ≠ AD) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h =
    Triangle.area △ g:k:e + Triangle.area △ g:e:f := by
  euclid_intros
  euclid_apply (helper_2_positions a b c d e f g h k AB DE AD BE CF HK BD)
  -- the two parallels prop_43 needs: HK ∥ DE and CF ∥ BE
  euclid_apply (proposition_30 HK DE AB)
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (proposition_43 d a b e h k c f g DE AB AD BE BD HK CF)
  -- convert each complement's diagonal-split to the one the claim uses
  euclid_apply (parallelogram_area a c h g AB HK AD CF)
  euclid_apply (parallelogram_area g k f e HK DE CF BE)
  euclid_finish

end Elements.Book2
