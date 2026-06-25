import SystemE

namespace Elements.Book1

/- 1.6.5: DB equals AC (the construction), and BC equals CB (segment symmetry). `|(d─b)| = |(a─c)|`
   follows from the proposition_3 postcondition `|(b─d)| = |(a─c)|` plus segment symmetry
   (|(d─b)| = |(b─d)|); `|(b─c)| = |(c─b)|` is segment symmetry alone. -/
set_option systemE.solverTime 30 in
theorem helper_1_6_step5 (a b c d : Point) (hbdac : |(b─d)| = |(a─c)|) :
    |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)| := by
  euclid_finish

end Elements.Book1
