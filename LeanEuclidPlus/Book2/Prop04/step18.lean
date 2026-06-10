import SystemE
import Book.Prop29
import Book.Prop30
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.18: HF (corners H,G,F,D) is also a square, "for the same reasons".
-- HGFD is a parallelogram (H,G on HK; D,F on DE; H,D on AD; G,F on CF):
--   * opposite sides + angles equal [1.34];
--   * adjacent sides equal: |HG| = |AC| (prop_34' on AHGC); |HD| = |AC| via |AH| = |CG| = |CB|
--     (step17), |AD| = |AB|, between a h d (from positions) & between a c b;
--   * one right angle ∠DHG = ∟: AD ⊥ AB (∠BAD = ∟), HK ∥ AB ⟹ AD ⊥ HK (corresponding angle [1.29]);
--     a parallelogram with one right angle has all four.
-- The betweenness `between a h d` is obtained from helper_2_positions (not assumed).
set_option systemE.solverTime 30 in
theorem helper_2_step18 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hbAB : b.onLine AB)
    (hdAD : d.onLine AD) (heBE : e.onLine BE) (hbBE : b.onLine BE)
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
    (haAD : a.onLine AD) (haAB : a.onLine AB) (hac : a ≠ c)
    (hbad : ∠ b:a:d = ∟) (hadab : |(a─d)| = |(a─b)|)
    (hstep17 : |(c─g)| = |(c─b)|) :
    (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
    (∠ d:h:g = ∟ ∧ ∠ h:g:f = ∟ ∧ ∠ g:f:d = ∟ ∧ ∠ f:d:h = ∟) := by
  euclid_intros
  -- positional facts (in particular between a h d)
  euclid_apply (helper_2_positions a b c d e f g h k AB DE AD BE CF HK BD)
  -- HK ∥ DE (for the HGFD parallelogram)
  euclid_apply (proposition_30 HK DE AB)
  -- AHGC parallelogram: |AC| = |HG| and |AH| = |CG|  [1.34]
  euclid_apply (proposition_34' a c h g AB HK AD CF)
  -- HGFD parallelogram: opposite sides + angles  [1.34]
  euclid_apply (proposition_34' h g d f HK DE AD CF)
  euclid_assert |(h─d)| = |(a─c)|
  -- right angle at H: AD ⊥ HK via corresponding angles (HK ∥ AB cut by AD)
  euclid_apply (proposition_29'''' g b d h a HK AB AD)
  euclid_finish

end Elements.Book2
