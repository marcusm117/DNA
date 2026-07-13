import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Triangle f-b-g: sides fb ⊂ AB, bg ⊂ GB, gf ⊂ FG.  Distinct lines: g ∈ GB off AB, b ∈ GB off FG,
-- g0 ∈ FG off AB.
theorem helper_3_33_hb_circ_gab_tri2
    (a b f g g0 : Point) (AB FG GB : Line)
    (haab : a.onLine AB) (hbab : b.onLine AB) (hafb : between a f b)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (hgFG : g.onLine FG) (hgGB : g.onLine GB) (hbGB : b.onLine GB)
    (hga : g ≠ a) (hgb : g ≠ b) (hgoffAB : ¬ g.onLine AB) (hboffFG : ¬ b.onLine FG) :
    formTriangle f b g AB GB FG := by
  euclid_finish

end Elements.Book3
