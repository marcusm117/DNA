import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.9 sub: g ∉ AB. g lies on BD (the diagonal), with b ∈ BD ∩ AB. If g ∈ AB then b, g are two
   common points of AB and BD; with b ≠ g this forces AB = BD, putting d (∈ BD) on AB. But d ∉ AB
   (a, b, d collinear with the right angle ∠ b:a:d = ∟ is impossible). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step9_gnab (a b d g : Point) (AB BD : Line)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hbg : b ≠ g) (hdnAB : ¬(d.onLine AB)) :
    ¬(g.onLine AB) := by
  intro hgAB
  euclid_apply (two_points_determine_line b g AB BD)
  euclid_finish

end Elements.Book2
