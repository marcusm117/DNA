import SystemE
import Book.Prop30
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

-- 2.4.6: opposite sides of parallelogram CGKB equal: CB = GK and CG = KB  [Prop.~1.34].
-- CGKB = parallelogram (c,b on AB; g,k on HK; c,g on CF; b,k on BE). Need CF ∥ BE: from
-- CF ∥ AD (step1) and AD ∥ BE (opposite sides of square ADEB) via [1.30]. Then proposition_34'.
set_option systemE.solverTime 30 in
theorem helper_2_step6 (a b c d e g k : Point) (AB DE AD BE CF HK : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hcb : distinctPointsOnLine c b AB) (hgk : distinctPointsOnLine g k HK)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hbBE : b.onLine BE) (hkBE : k.onLine BE)
    (hcg_side : c.sameSide g BE)
    (hADCF : AD ≠ CF) (hbk : b ≠ k)
    (hCFAD : ¬(CF.intersectsLine AD)) (hABHK : ¬(AB.intersectsLine HK)) :
    |(c─b)| = |(g─k)| ∧ |(c─g)| = |(k─b)| := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (proposition_34' c b g k AB HK CF BE)
  euclid_finish

end Elements.Book2
