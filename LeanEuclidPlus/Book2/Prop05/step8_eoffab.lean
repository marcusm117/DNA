import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub (root off-line fact): ¬(e.onLine AB). b,c on AB, ∠ b:c:e = ∟. If e ∈ AB then
   b,c,e are collinear on AB, so the angle ∠ b:c:e at c is degenerate — either 0 (e not
   separated from b by c) or flat 2∟ (between b c e) — neither of which is a single right
   angle. Proven explicitly (degenerated_angle_if / flat_angle_onlyif), no bare euclid_finish. -/
theorem helper_2_5_step8_eoffab (a b c d e : Point) (AB : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hacd : between a c d) (hcdb : between c d b)
    (hcelen : |(c─e)| = |(c─b)|)
    (hbce : ∠ b:c:e = ∟) :
    ¬(e.onLine AB) := by
  intro heAB
  have hbc : b ≠ c := by euclid_finish
  -- c ≠ e: the square side ce equals cb ≠ 0, so c and e are distinct
  have hce : c ≠ e := by
    intro heq
    rw [heq] at hcelen
    euclid_finish
  by_cases hbtw : between b c e
  · -- flat angle: ∠ b:c:e = 2∟, contradicting = ∟
    euclid_apply (flat_angle_onlyif b c e)
    euclid_finish
  · -- degenerate (collinear, not separated): ∠ b:c:e = 0, contradicting = ∟
    euclid_apply (degenerated_angle_if b c e AB)
    euclid_finish

end Elements.Book2
