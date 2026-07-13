import SystemE
import Book3.Prop32.Main
import Book3.Prop33.step14_c2_c2opp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Same as step14_c1 but with the other FG∩α point c2 (when c1 is NOT on the far side of AB from d0,
-- c2 is — because FG is a diameter through the centre g, so c1 and c2 lie on opposite sides of AB).
theorem helper_3_33_step14_c2
    (a b d d0 e f g g0 c1 c2 : Point) (AB AD FG : Line) (α : Circle)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hd0ad : d0.onLine AD) (hdad0 : between d a d0)
    (hacirc : a.onCircle α) (hbcirc : b.onCircle α) (hecirc : e.onCircle α)
    (hc1circ : c1.onCircle α) (hc2circ : c2.onCircle α)
    (hc1FG : c1.onLine FG) (hc2FG : c2.onLine FG) (hc12 : c1 ≠ c2)
    (hg0off : ¬ g0.onLine AB) (hg0FG : g0.onLine FG)
    (hgcen : g.isCentre α) (hgFG : g.onLine FG) (hfFG : f.onLine FG) (hafb : between a f b)
    (hADtangent : ¬ AD.intersectsCircle α)
    (heoffAB : ¬ e.onLine AB) (hdoffAB : ¬ d.onLine AB) (hedss : ¬ e.sameSide d AB)
    (hc1not : ¬ c1.opposingSides d0 AB) :
    ∠ d:a:b = ∠ a:e:b := by
  have hd0offAB : ¬ d0.onLine AB := by euclid_finish
  have step14_c2_c2opp : c2.opposingSides d0 AB := by euclid_apply (helper_3_33_step14_c2_c2opp a b d0 f g g0 c1 c2 AB FG α (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show c1.onCircle α; assumption)) (by euclid_assumption "" (show c2.onCircle α; assumption)) (by euclid_assumption "" (show c1.onLine FG; assumption)) (by euclid_assumption "" (show c2.onLine FG; assumption)) (by euclid_assumption "" (show c1 ≠ c2; assumption)) (by euclid_assumption "" (show ¬ d0.onLine AB; assumption)) (by euclid_assumption "" (show ¬ c1.opposingSides d0 AB; assumption)))
  euclid_apply (proposition_32 a e b c2 d0 d α AD AB)
  euclid_finish

end Elements.Book3
