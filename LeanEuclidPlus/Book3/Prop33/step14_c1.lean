import SystemE
import Book3.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Apply proposition_32 with the FG∩α point c1 (on the far side of AB from d0) as the second
-- segment point: ∠(f=d):(b=a):(d=b) = ∠(b=a):(a=e):(d=b), i.e. ∠d:a:b = ∠a:e:b.
theorem helper_3_33_step14_c1
    (a b d d0 e c1 : Point) (AB AD : Line) (α : Circle)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hd0ad : d0.onLine AD) (hdad0 : between d a d0)
    (hacirc : a.onCircle α) (hbcirc : b.onCircle α) (hecirc : e.onCircle α) (hc1circ : c1.onCircle α)
    (hADtangent : ¬ AD.intersectsCircle α) (hstep3 : ∠ d:a:e = ∟)
    (heoffAB : ¬ e.onLine AB) (hdoffAB : ¬ d.onLine AB) (hedss : ¬ e.sameSide d AB)
    (hc1 : c1.opposingSides d0 AB) :
    ∠ d:a:b = ∠ a:e:b := by
  euclid_apply (proposition_32 a e b c1 d0 d α AD AB)
  euclid_finish

end Elements.Book3
