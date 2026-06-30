import SystemE

namespace Elements.Book2

open Elements

-- ¬h.onLine BE : if h were on BE then h, e, b₀ would be collinear and ∠b₀:e:h would be 0 or 2∟,
-- not ∟. So the right angle ∠b₀:e:h = ∟ (step14_rt0) forces h off BE. (e ≠ b₀ from between b₀ e f,
-- h ≠ e from between h e d.)
set_option systemE.solverTime 30 in
theorem helper_2_14_step14_hoff (e b₀ h d f : Point) (BE : Line)
    (h_eBE : e.onLine BE) (h_b0BE : b₀.onLine BE) (h_rt0 : ∠ b₀:e:h = ∟)
    (h_bef : between b₀ e f) (h_bet_hed : between h e d) :
    ¬ h.onLine BE := by
  intro hon
  euclid_finish

end Elements.Book2
