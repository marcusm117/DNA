import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_2_step2 (d a b : Point) (DA AB DB : Line)
    (h1 : d.onLine DA) (h2 : a.onLine DA)
    (h3 : a.onLine AB) (h4 : b.onLine AB)
    (h5 : d.onLine DB) (h6 : b.onLine DB)
    (h7 : |(d─a)| = |(a─b)|) (h8 : |(d─b)| = |(a─b)|)
    (hab : a ≠ b) :
    formTriangle d a b DA AB DB ∧ |(d─a)| = |(a─b)| ∧ |(d─b)| = |(a─b)| := by
  euclid_finish

end Elements.Book1
