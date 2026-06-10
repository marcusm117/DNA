import SystemE
import Book.Prop30

namespace Elements.Book2

open Elements.Book1

-- Shared positional facts for Prop 2.4. From the bare construction outputs, derive the six
-- betweenness facts the area steps need (intersection_lines does NOT give them). Each is a
-- pasch_4: the crossing line separates the two endpoints, so the intersection lies between them.
set_option systemE.solverTime 30 in
theorem helper_2_positions (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
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
    -- distinctness facts (all from the figure; supplied by Main)
    (hbd : b ≠ d) (hbg : b ≠ g) (hdg : d ≠ g) (hCFBD : CF ≠ BD)
    (hah : a ≠ h) (hdh : d ≠ h) (hADHK : AD ≠ HK)
    (hbk : b ≠ k) (hek : e ≠ k) (hBEHK : BE ≠ HK)
    (hdf : d ≠ f) (hef : e ≠ f) (hDECF : DE ≠ CF)
    (hcg : c ≠ g) (hfg : f ≠ g) (hCFHK : CF ≠ HK)
    (hhg : h ≠ g) (hkg : k ≠ g) (hHKCF : HK ≠ CF)
    (hHKDE : HK ≠ DE) (hABHKne : AB ≠ HK) (hCFBE : CF ≠ BE) (hADCFne : AD ≠ CF) :
    between a h d ∧ between b k e ∧ between d f e ∧
    between b g d ∧ between c g f ∧ between h g k := by
  euclid_intros
  -- derive HK ∥ DE (from AB ∥ HK and AB ∥ DE) and CF ∥ BE (from AD ∥ CF and AD ∥ BE)
  euclid_apply (proposition_30 HK DE AB)
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (pasch_4 b g d CF BD)   -- BD cut by CF
  euclid_apply (pasch_4 a h d HK AD)   -- AD cut by HK
  -- B above HK (AB ∥ HK), E below HK (DE ∥ HK) ⟹ opposite sides
  euclid_assert ¬(b.sameSide e HK)
  euclid_apply (pasch_4 b k e HK BE)   -- BE cut by HK
  -- D left of CF (AD ∥ CF), E right of CF ⟹ opposite sides
  euclid_assert ¬(d.sameSide e CF)
  euclid_apply (pasch_4 d f e CF DE)   -- DE cut by CF
  euclid_apply (pasch_4 c g f HK CF)   -- CF cut by HK
  euclid_apply (pasch_4 h g k CF HK)   -- HK cut by CF
  euclid_finish

end Elements.Book2
