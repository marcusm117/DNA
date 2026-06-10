import SystemE

namespace Elements.Book2

-- 2.4.4: ∠CGB = ∠GBC, by transitivity. From step2 (∠CGB = ∠ADB) and step3 (∠ADB = ∠ABD),
-- and the angle identities ∠ABD = ∠GBC (g on BD between b,d so ray BG = ray BD; a,c with C between
-- a,b so ∠ABD locates the same rays as ∠GBC). euclid_finish reconciles the ray identities.
set_option systemE.solverTime 30 in
theorem helper_2_step4 (a b c d g : Point) (AB BD CF : Line)
    (hab : distinctPointsOnLine a b AB) (hbd : distinctPointsOnLine b d BD)
    (hcab : c.onLine AB) (hacb : between a c b)
    (hbgd : between b g d) (hgCF : g.onLine CF) (hcCF : c.onLine CF)
    (hstep2 : ∠ c:g:b = ∠ a:d:b) (hstep3 : ∠ a:d:b = ∠ a:b:d) :
    ∠ c:g:b = ∠ g:b:c := by
  euclid_intros
  euclid_finish

end Elements.Book2
