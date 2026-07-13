import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Triangle f-a-g: sides fa ⊂ AB, ag ⊂ AG, gf ⊂ FG.  Distinct lines: g ∈ AG off AB, a ∈ AG off FG,
-- g0 ∈ FG off AB.
theorem helper_3_33_hb_circ_gab_tri1
    (a b f g g0 : Point) (AB FG AG : Line)
    (haab : a.onLine AB) (hbab : b.onLine AB) (hafb : between a f b)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (hgFG : g.onLine FG) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hga : g ≠ a) (hgb : g ≠ b) (hgoffAB : ¬ g.onLine AB) (haoffFG : ¬ a.onLine FG) :
    formTriangle f a g AB AG FG := by
  euclid_finish

end Elements.Book3
