import SystemE

namespace Elements.Book1

/-
Helper for Prop48.lean:23  `|(d─c)| = |(b─c)|`, which times out in the full proof context.

Purely algebraic: from Pythagoras on triangle a-d-c (h), |d─a| = |a─b| (sq), and the
original hypothesis, both |(d─c)|² and |(b─c)|² equal |(a─b)|² + |(a─c)|²; lengths are
nonnegative, so |(d─c)| = |(b─c)|.  No geometry — just the three length equations.
-/
theorem helper_48_dc_eq_bc :
    ∀ (a b c d : Point),
    |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| ∧
    |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)| ∧
    |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| →
    |(d─c)| = |(b─c)| :=
by
  euclid_intros
  euclid_finish

end Elements.Book1
