import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: b ∉ HF. b lies on AB, which is parallel to HF (¬HF.intersectsLine AB) and distinct
   from it (g ∈ HF but g ∉ AB). A common point b of HF and AB would make them intersect. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_bnhf (b g : Point) (AB HF : Line)
    (hbAB : b.onLine AB) (hgHF : g.onLine HF) (hgnAB : ¬(g.onLine AB))
    (hHFAB : ¬(HF.intersectsLine AB)) :
    ¬(b.onLine HF) := by
  intro hbHF
  have hne : HF ≠ AB := fun h => hgnAB (h ▸ hgHF)
  euclid_apply (intersection_lines_common_point b HF AB)
  euclid_finish

end Elements.Book2
