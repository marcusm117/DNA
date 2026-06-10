import SystemE

namespace Elements.Book2

-- 2.4.11: ∠KBC = ∟. At B: ray BC = ray BA (C between A,B), ray BK = ray BE (K on BE),
-- and ∠ABE = ∟ (square ADEB). So ∠KBC = ∠ABE = ∟.
set_option systemE.solverTime 30 in
theorem helper_2_step11 (a b c e k : Point) (AB BE : Line)
    (hab : distinctPointsOnLine a b AB) (hcab : c.onLine AB) (hacb : between a c b)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hkBE : k.onLine BE)
    (hbek : between b k e ∨ between b e k ∨ k = e)
    (habe : ∠ a:b:e = ∟) (hbk : b ≠ k) :
    ∠ k:b:c = ∟ := by
  euclid_intros
  euclid_finish

end Elements.Book2
