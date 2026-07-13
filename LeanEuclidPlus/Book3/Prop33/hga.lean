import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- g ≠ a: g lies on FG, but a is off FG (a, f on both AB and FG would force AB = FG, yet g0 ∈ FG
-- is off AB).
theorem helper_3_33_hga
    (a b f g g0 : Point) (AB FG : Line)
    (haab : a.onLine AB) (hbab : b.onLine AB) (hafb : between a f b)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (hgFG : g.onLine FG) :
    g ≠ a := by
  have haoffFG : ¬ a.onLine FG := by euclid_finish
  exact fun h => haoffFG (h ▸ hgFG)

end Elements.Book3
