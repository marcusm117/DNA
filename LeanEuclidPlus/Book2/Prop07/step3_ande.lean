import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: a ∉ DE. a lies on AB, which is parallel to DE (¬DE.intersectsLine AB) and distinct
   from it (d ∈ DE but d ∉ AB). A common point a of DE and AB would make them intersect. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_ande (a d : Point) (AB DE : Line)
    (haAB : a.onLine AB) (hdDE : d.onLine DE) (hdnAB : ¬(d.onLine AB))
    (hDEAB : ¬(DE.intersectsLine AB)) :
    ¬(a.onLine DE) := by
  intro haDE
  have hne : DE ≠ AB := fun h => hdnAB (h ▸ hdDE)
  euclid_apply (intersection_lines_common_point a DE AB)
  euclid_finish

end Elements.Book2
