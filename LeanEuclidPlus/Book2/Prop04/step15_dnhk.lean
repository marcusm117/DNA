import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.15 sub: d ∉ HK. d lies on BD, with g ∈ BD ∩ HK. If d ∈ HK then d, g are two common points of
   BD and HK; with d ≠ g this forces BD = HK, putting b (∈ BD) on HK — but b ∉ HK. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step15_dnhk (b d g : Point) (BD HK : Line)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK)
    (hdg : d ≠ g) (hbnHK : ¬(b.onLine HK)) :
    ¬(d.onLine HK) := by
  intro hdHK
  euclid_apply (two_points_determine_line d g BD HK)
  euclid_finish

end Elements.Book2
