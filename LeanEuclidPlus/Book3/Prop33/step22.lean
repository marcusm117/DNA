import SystemE
import Book3.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- AD touches the circle (Prop 3.16 corr.): AB is a diameter (centre f, between a f b), and AD is at
-- right angles to it at the extremity a (∠b:a:d = ∟).  Apply proposition_16 with touch a, opposite
-- end b, centre f, tangent point d.
theorem helper_3_33_step22
    (a b d f : Point) (AD : Line) (α : Circle)
    (hfcen : f.isCentre α) (hacirc : a.onCircle α) (hb_circ_2 : b.onCircle α)
    (hafb : between a f b) (haad : a.onLine AD) (hdad : d.onLine AD) (hadd : d ≠ a)
    (hassump1 : ∠ b:a:d = ∟)   -- "the angle at $A$ being a right-angle"
    : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α := by
  euclid_apply (proposition_16 a b f d α AD)
  euclid_finish

end Elements.Book3
