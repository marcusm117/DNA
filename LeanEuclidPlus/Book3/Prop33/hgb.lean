import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- g ≠ b: g lies on FG, but b is off FG (b, f on both AB and FG would force AB = FG, yet g0 ∈ FG
-- is off AB).
theorem helper_3_33_hgb
    (a b f g g0 : Point) (AB FG : Line)
    (haab : a.onLine AB) (hbab : b.onLine AB) (hafb : between a f b)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (hgFG : g.onLine FG) :
    g ≠ b := by
  have hboffFG : ¬ b.onLine FG := by euclid_finish
  exact fun h => hboffFG (h ▸ hgFG)

end Elements.Book3
