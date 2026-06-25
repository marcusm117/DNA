import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.26 sub: g ∉ AD. g, d lie on BD with d ∈ AD; if g ∈ AD then g, d are two common points of BD
   and AD (g ≠ d), so BD = AD, putting b on AD — but b ∉ AD. -/
theorem helper_2_4_step26_gnad (b d g : Point) (AD BD : Line)
    (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgd : g ≠ d) (hbnAD : ¬(b.onLine AD)) :
    ¬(g.onLine AD) := by
  euclid_intros
  euclid_finish

end Elements.Book2
