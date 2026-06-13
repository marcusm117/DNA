import SystemE

namespace Elements.Book2

-- 2.4.25: "HF and CK are the squares on AC and CB" — identical claim to 2.4.20; reuse helper_2_step20.
set_option systemE.solverTime 30 in
theorem helper_2_step25 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
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
  have positions : between a h d ∧ between b k e ∧ between d f e ∧
      between b g d ∧ between c g f ∧ between h g k := by sorry
  have area_accb :
      (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:b:k + Triangle.area △ c:k:g = |(c─b)| * |(c─b)|) := by sorry
  euclid_finish

end Elements.Book2
