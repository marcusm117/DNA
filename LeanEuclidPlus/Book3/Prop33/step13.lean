import SystemE
import Book3.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- AD touches the circle (Prop 3.16 corr.): AD is at right angles to the diameter AE = a-g-e at
-- its extremity a (∠d:a:e = ∟).  Apply proposition_16 with touch point a, centre g, opposite end
-- e, and tangent point d on AD.
theorem helper_3_33_step13
    (a d e g : Point) (AD : Line) (α : Circle)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α) (he_circ : e.onCircle α)
    (hega : between e g a) (haad : a.onLine AD) (hdad : d.onLine AD) (hadd : d ≠ a)
    (step13_assumption1 : ∠ d:a:e = ∟) :
    (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α := by
  euclid_apply (proposition_16 a e g d α AD)
  euclid_finish

end Elements.Book3
