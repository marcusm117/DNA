import SystemE
import Book3.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Tangent-chord (Prop 3.32): AD touches α at a (step38), AB is a chord.  Apply proposition_32 with
-- inscribed vertex h (in the alternate segment, opposite d) and the other FG∩α point h' (opposite the
-- back tangent point d0): ∠b:a:d = ∠a:h:b.
theorem helper_3_33_step39
    (a b d d0 h h' : Point) (AB AD : Line) (α : Circle)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hd0ad : d0.onLine AD) (hdad0 : between d a d0)
    (hacirc : a.onCircle α) (hbcirc : b.onCircle α)
    (hh_circ : h.onCircle α) (hh_side : h.opposingSides d AB)
    (hh'_circ : h'.onCircle α) (hh'_side : h'.opposingSides d0 AB)
    (hstep38 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α)
    (hassump1 : a.onLine AB ∧ b.onLine AB ∧ b.onCircle α)   -- "$AB$ has been drawn across (the circle) from the point of contact $A$"
    : ∠ b:a:d = ∠ a:h:b := by
  have hADtangent : ¬ AD.intersectsCircle α := hstep38.2
  euclid_apply (proposition_32 a h b h' d0 d α AD AB)
  euclid_finish

end Elements.Book3
