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
theorem helper_2_step9 (a b c d e g k : Point) (AB DE AD BE CF HK : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hba : distinctPointsOnLine b a AB) (hcab : c.onLine AB) (hacb : between a c b)
    (had : distinctPointsOnLine a d AD) (hcg : distinctPointsOnLine c g CF)
    (hcb' : distinctPointsOnLine c b AB) (hgk : distinctPointsOnLine g k HK)
    (hgCF : g.onLine CF) (hbBE : b.onLine BE) (hkBE : k.onLine BE)
    (hcg_side : c.sameSide g BE) (hgd_side : g.sameSide d AB)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟)
    (hbek : between b k e ∨ between b e k ∨ k = e) (hbk : b ≠ k)
    (hpar : ¬(CF.intersectsLine AD)) (hADCF : AD ≠ CF) (hABHK : ¬(AB.intersectsLine HK)) :
    ∠ b:c:g = ∟ ∧ ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ ∧ ∠ k:b:c = ∟ := by
  euclid_intros
  -- ∠BCG = ∟ via corresponding angles (CF ∥ AD cut by AB)
  euclid_apply (proposition_29'''' g d b c a CF AD AB)
  -- CF ∥ BE (CF ∥ AD, AD ∥ BE) so CGKB is a parallelogram; opposite angles equal [1.34]
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (proposition_34' c b g k AB HK CF BE)
  euclid_finish

end Elements.Book2
