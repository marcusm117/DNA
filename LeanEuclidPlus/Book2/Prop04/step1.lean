import SystemE

namespace Elements.Book2

-- 2.4.1: square ADEB on AB [1.46]; BD joined; CF through C ∥ AD, HK through G ∥ AB [1.31].
-- The claim is exactly the construction outputs; the citations [1.46]/[1.31] are recorded in
-- Main, where proposition_46 / proposition_31 are euclid_applied in this sentence's block.
set_option systemE.solverTime 30 in
theorem helper_2_step1 (a b c d e g : Point) (AB DE AD BE CF HK : Line)
    (hde : |(d─e)| = |(a─b)|) (had : |(a─d)| = |(a─b)|) (hbe : |(b─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (hade : ∠ a:d:e = ∟) (habe : ∠ a:b:e = ∟) (hbed : ∠ b:e:d = ∟)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hgHK : g.onLine HK) (hHKAB : ¬(HK.intersectsLine AB)) :
    |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧ |(d─e)| = |(a─b)| ∧
    (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) ∧
    c.onLine CF ∧ ¬(CF.intersectsLine AD) ∧
    g.onLine HK ∧ ¬(HK.intersectsLine AB) := by
  euclid_intros
  euclid_finish

end Elements.Book2
