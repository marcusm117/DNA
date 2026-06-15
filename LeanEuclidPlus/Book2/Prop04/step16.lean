import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.16: ∠ b:c:g = ∟. From ∠ k:b:c + ∠ g:c:b = ∟ + ∟ (step14) and ∠ k:b:c = ∟ (step15) we get
   ∠ g:c:b = ∟; then ∠ b:c:g = ∠ g:c:b by angle symmetry. -/
theorem helper_2_4_step16 (a b c g k : Point)
    (hacb : between a c b)
    (hstep8 : |(b─c)| = |(c─g)|)
    (hstep14 : ∠ k:b:c + ∠ g:c:b = ∟ + ∟)
    (hstep15 : ∠ k:b:c = ∟) :
    ∠ b:c:g = ∟ := by
  -- b ≠ c (c strictly between a and b); c ≠ g (else |b─c| = |c─g| = 0)
  have hbc : b ≠ c := by euclid_finish
  have hcg : c ≠ g := by euclid_finish
  have hsym : (∠ b:c:g : ℝ) = ∠ g:c:b := angle_symm b c g ⟨hbc, hcg⟩
  rw [hsym]
  euclid_finish

end Elements.Book2
