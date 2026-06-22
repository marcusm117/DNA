import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: d ∉ HF. d, g lie on BD with g ∈ HF; if d ∈ HF then d, g are two common points of BD
   and HF (g ≠ d), so BD = HF, putting b (∈ BD) on HF — but b ∉ HF. -/
theorem helper_2_7_step3_dnhf (b d g : Point) (BD HF : Line)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHF : g.onLine HF)
    (hgd : g ≠ d) (hbnHF : ¬(b.onLine HF)) :
    ¬(d.onLine HF) := by
  intro hdHF
  euclid_apply (two_points_determine_line g d BD HF)
  euclid_finish

end Elements.Book2
