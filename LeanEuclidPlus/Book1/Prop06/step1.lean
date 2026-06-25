import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.1: If AB is unequal to AC then one of them is greater. Trichotomy of the two
   real-valued lengths from the assumed disequality hne. Pure real arithmetic, no SMT. -/
theorem helper_1_6_step1 (a b c : Point) (hne : |(a─b)| ≠ |(a─c)|) :
    |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr h
  · exact Or.inl h

end Elements.Book1
