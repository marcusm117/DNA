import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- c2 is on the far side of AB from d0. FG is a diameter through the centre g and meets AB at the
-- interior point f (midpoint of chord ab), so the two intersections c1, c2 straddle AB (between c1 f
-- c2). Since c1 is NOT opposite d0 (else branch), c1 is on d0's side, hence c2 is on the far side.
theorem helper_3_33_step14_c2_c2opp
    (a b d0 f g g0 c1 c2 : Point) (AB FG : Line) (α : Circle)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (hafb : between a f b) (hfFG : f.onLine FG)
    (hg0off : ¬ g0.onLine AB) (hg0FG : g0.onLine FG)
    (hgcen : g.isCentre α) (hgFG : g.onLine FG)
    (hacirc : a.onCircle α) (hbcirc : b.onCircle α)
    (hc1circ : c1.onCircle α) (hc2circ : c2.onCircle α)
    (hc1FG : c1.onLine FG) (hc2FG : c2.onLine FG) (hc12 : c1 ≠ c2)
    (hd0offAB : ¬ d0.onLine AB)
    (hc1not : ¬ c1.opposingSides d0 AB) :
    c2.opposingSides d0 AB := by
  have hfin : f.insideCircle α := by
    euclid_apply (circle_points_between a b f α)
    euclid_finish
  have hfAB : f.onLine AB := by euclid_finish
  have hABFGne : AB ≠ FG := by euclid_finish
  have hc1offAB : ¬ c1.onLine AB := by euclid_finish
  have hc2offAB : ¬ c2.onLine AB := by euclid_finish
  have hbetween : between c1 f c2 := by euclid_finish
  euclid_apply (pasch_3 c1 f c2 AB)
  euclid_finish

end Elements.Book3
