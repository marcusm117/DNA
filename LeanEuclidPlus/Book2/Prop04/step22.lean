import SystemE
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.22: AG is the rectangle contained by AC and CB: area(AG) = |AC|·|CB|.
-- AG = AHGC, right-angled (∠AHG = ∟, from step18); rectangle_area ⟹ area = |AC|·|AH|, and
-- |AH| = |CG| = |CB| (parallelogram AHGC opposite sides [1.34], step17). Positions pins orientation.
set_option systemE.solverTime 30 in
theorem helper_2_step22 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
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
    (hac : a ≠ c)
    (hahg : ∠ a:h:g = ∟)
    (hstep17 : |(c─g)| = |(c─b)|) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h = |(a─c)| * |(c─b)| := by
  euclid_intros
  have positions : between a h d ∧ between b k e ∧ between d f e ∧
      between b g d ∧ between c g f ∧ between h g k := by sorry
  euclid_apply (proposition_34' a c h g AB HK AD CF)
  euclid_assert |(a─h)| = |(c─b)|
  euclid_apply (rectangle_area a c h g AB HK AD CF)
  euclid_finish

end Elements.Book2
