import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.4: DC joined [Post.~1]. The `line_from_points d c` construction in Main produces the line `DC`
   with `d.onLine DC` and `c.onLine DC`; this helper repackages those two incidence facts. -/
theorem helper_1_6_step4 (d c : Point) (DC : Line) (hd : d.onLine DC) (hc : c.onLine DC) :
    d.onLine DC ∧ c.onLine DC := by
  exact ⟨hd, hc⟩

end Elements.Book1
