import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: d ∉ HK. d, g lie on BD with g ∈ HK; if d ∈ HK then d, g are two common points of BD
   and HK (g ≠ d), so BD = HK, putting b (∈ BD) on HK — but b ∉ HK. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step22_dnhk (b d g : Point) (BD HK : Line)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK)
    (hgd : g ≠ d) (hbnHK : ¬(b.onLine HK)) :
    ¬(d.onLine HK) := by
  intro hdHK
  euclid_apply (two_points_determine_line g d BD HK)
  euclid_finish

end Elements.Book2
