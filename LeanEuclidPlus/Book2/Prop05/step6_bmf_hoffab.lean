import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: ¬h.onLine AB. h ∈ BE and b ∈ BE ∩ AB; BE ≠ AB (e ∈ BE is off AB) and h ≠ b
   (h ∈ DG, b ∉ DG), so if h were on AB the two distinct lines AB, BE would share both b and h —
   forcing AB = BE → e ∈ AB → contradiction. -/
theorem helper_2_5_step6_bmf_hoffab (b e h : Point) (AB BE DG : Line)
    (hbAB : b.onLine AB) (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hhDG : h.onLine DG)
    (heoffAB : ¬(e.onLine AB)) (hboffDG : ¬(b.onLine DG)) :
    ¬(h.onLine AB) := by
  intro hhAB
  have hBEneAB : BE ≠ AB := fun heq => heoffAB (heq ▸ heBE)
  have hhb : h ≠ b := fun heq => hboffDG (heq ▸ hhDG)
  euclid_apply (two_points_determine_line h b BE AB)
  euclid_finish

end Elements.Book2
