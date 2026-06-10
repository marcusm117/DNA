import SystemE
import Book.Prop29

namespace Elements.Book2

open Elements.Book1

-- 2.4.12: ∠BCG = ∟. CF ∥ AD and AD ⊥ AB (∠BAD = ∟ in square ADEB), so CF ⊥ AB. Corresponding
-- angles [1.29]: parallels CF, AD cut by transversal AB at c, a; g and d on the SAME side of AB
-- (both below the top edge). proposition_29'''' gives ∠BCG = ∠CAD = ∠BAD = ∟.
set_option systemE.solverTime 30 in
theorem helper_2_step12 (a b c d g : Point) (AB AD CF : Line)
    (hba : distinctPointsOnLine b a AB) (hcab : c.onLine AB) (hacb : between a c b)
    (had : distinctPointsOnLine a d AD) (hcg : distinctPointsOnLine c g CF)
    (hgd_side : g.sameSide d AB)
    (hbad : ∠ b:a:d = ∟) (hpar : ¬(CF.intersectsLine AD)) :
    ∠ b:c:g = ∟ := by
  euclid_intros
  euclid_apply (proposition_29'''' g d b c a CF AD AB)
  euclid_finish

end Elements.Book2
