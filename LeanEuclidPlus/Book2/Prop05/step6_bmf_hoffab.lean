import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: ¬h.onLine AB. h ∈ BE and b ∈ BE ∩ AB; BE ≠ AB (e ∈ BE is off AB) and h ≠ b
   (between b h e), so if h were on AB the two distinct lines AB, BE would share both b and h —
   impossible. b≠h from between b h e; BE≠AB from e∉AB. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_bmf_hoffab (b e h : Point) (AB BE : Line)
    (hbAB : b.onLine AB) (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heoffAB : ¬(e.onLine AB)) (hbhe : between b h e) :
    ¬(h.onLine AB) := by
  intro hhAB
  have hbe_ne_ab : BE ≠ AB := fun heq => heoffAB (heq ▸ heBE)
  euclid_finish

end Elements.Book2
