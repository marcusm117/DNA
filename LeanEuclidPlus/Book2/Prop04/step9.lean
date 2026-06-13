import SystemE
import Book.Prop29
import Book.Prop30
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.9: CGKB is right-angled — all four angles right. Derived from the construction:
--   ∠KBC = ∟  : at B, ray BK = ray BE, ray BC = ray BA, ∠ABE = ∟ (square ADEB).
--   ∠BCG = ∟  : CF ∥ AD ⊥ AB ⟹ corresponding angle ∠BCG = ∠BAD = ∟  [1.29].
--   opposite angles of parallelogram CGKB equal [1.34]: ∠CBK = ∠CGK and ∠BCG = ∠GKB,
--     so ∠CGK = ∠KBC = ∟ and ∠GKB = ∠BCG = ∟.
set_option systemE.solverTime 30 in
theorem helper_2_step9 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
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
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) :
    ∠ b:c:g = ∟ ∧ ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ ∧ ∠ k:b:c = ∟ := by
  euclid_intros
  -- betweenness facts (gives between b g d, between b k e — orientation of CGKB / BD)
  have positions : between a h d ∧ between b k e ∧ between d f e ∧
      between b g d ∧ between c g f ∧ between h g k := by sorry
  -- CF ∥ BE (CF ∥ AD, AD ∥ BE) so CGKB is a parallelogram; c,g on CF ⟹ c.sameSide g BE
  euclid_apply (proposition_30 CF BE AD)
  -- ∠BCG = ∟ via corresponding angles (CF ∥ AD cut by AB); g.sameSide d AB from between b g d
  euclid_apply (proposition_29'''' g d b c a CF AD AB)
  -- opposite angles of parallelogram CGKB equal [1.34]
  euclid_apply (proposition_34' c b g k AB HK CF BE)
  euclid_finish

end Elements.Book2
