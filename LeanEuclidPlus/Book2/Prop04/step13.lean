import SystemE
import Book.Prop30
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.13: opposite angles of parallelogram CGKB ⟹ ∠CGK and ∠GKB are right-angles [1.34].
-- proposition_34' on CGKB gives ∠CBK = ∠CGK and ∠BCG = ∠GKB; with ∠KBC = ∟ (step11) and
-- ∠BCG = ∟ (step12), both ∠CGK and ∠GKB are right.
set_option systemE.solverTime 30 in
theorem helper_2_step13 (a b c d e g k : Point) (AB DE AD BE CF HK : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hcb : distinctPointsOnLine c b AB) (hgk : distinctPointsOnLine g k HK)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hbBE : b.onLine BE) (hkBE : k.onLine BE)
    (hcg_side : c.sameSide g BE)
    (hADCF : AD ≠ CF) (hbk : b ≠ k)
    (hCFAD : ¬(CF.intersectsLine AD)) (hABHK : ¬(AB.intersectsLine HK))
    (hstep11 : ∠ k:b:c = ∟) (hstep12 : ∠ b:c:g = ∟) :
    ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (proposition_34' c b g k AB HK CF BE)
  euclid_finish

end Elements.Book2
