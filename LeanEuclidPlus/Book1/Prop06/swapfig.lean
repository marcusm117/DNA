import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6 WLOG reduction (AC > AB): the facts of the b↔c-swapped triangle needed to apply the main
   case `Hsym`. All but two are pure symmetry of the given figure; `a ≠ c` is a triangle-vertex
   distinctness (euclid_finish), and `|(a─c)| > |(a─b)|` follows from the disjunction `step1` and
   the WLOG negation `¬(|(a─b)| > |(a─c)|)`. -/
theorem helper_1_6_swapfig (a b c : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hang : ∠ a:b:c = ∠ a:c:b) (hne : |(a─b)| ≠ |(a─c)|)
    (hor : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)|)
    (hgt : ¬ |(a─b)| > |(a─c)|) :
    (∠ a:c:b = ∠ a:b:c)
    ∧ (a ≠ c)
    ∧ (AC ≠ BC)
    ∧ (BC ≠ AB)
    ∧ (AB ≠ AC)
    ∧ (|(a─c)| ≠ |(a─b)|)
    ∧ (|(a─c)| > |(a─b)| ∨ |(a─b)| > |(a─c)|)
    ∧ (|(a─c)| > |(a─b)|) := by
  refine ⟨hang.symm, ?_, hBCAC.symm, hABBC.symm, hACAB.symm, hne.symm, hor.symm, ?_⟩
  · euclid_finish
  · rcases hor with h | h
    · exact absurd h hgt
    · exact h

end Elements.Book1
