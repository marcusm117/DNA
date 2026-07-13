import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- h1, h2 (the two FG∩α points) straddle AB: FG is a diameter (through centre g), so it meets α at
-- two points with the interior chord-midpoint f between them (f is inside α, on both FG and AB), hence
-- h1, h2 lie on opposite sides of AB.
theorem helper_3_33_hh_straddle
    (a b f g g0 h1 h2 : Point) (AB FG : Line) (α : Circle)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hne : a ≠ b)
    (hafb : between a f b) (hfFG : f.onLine FG)
    (hg0off : ¬ g0.onLine AB) (hg0FG : g0.onLine FG)
    (hgcen : g.isCentre α) (hgFG : g.onLine FG)
    (hacirc : a.onCircle α) (hbcirc : b.onCircle α)
    (hh1circ : h1.onCircle α) (hh2circ : h2.onCircle α)
    (hh1FG : h1.onLine FG) (hh2FG : h2.onLine FG) (hh12 : h1 ≠ h2) :
    h1.opposingSides h2 AB := by
  have hfin : f.insideCircle α := by
    euclid_apply (circle_points_between a b f α)
    euclid_finish
  have hfAB : f.onLine AB := by euclid_finish
  have hABFGne : AB ≠ FG := by euclid_finish
  have hh1offAB : ¬ h1.onLine AB := by euclid_finish
  have hh2offAB : ¬ h2.onLine AB := by euclid_finish
  have hbetween : between h1 f h2 := by euclid_finish
  euclid_apply (pasch_3 h1 f h2 AB)
  euclid_finish

end Elements.Book3
