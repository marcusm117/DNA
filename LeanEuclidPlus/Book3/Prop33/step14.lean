import SystemE
import Book3.Prop33.step14_fgcirc
import Book3.Prop33.step14_edab
import Book3.Prop33.step14_c1
import Book3.Prop33.step14_c2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Tangent-chord angle (Prop 3.32): the other segment point c is a FG∩α point; split on which of
-- the two intersection points lies on the far side of AB from d0.
theorem helper_3_33_step14
    (a b d d0 e f g g0 : Point) (AB AD AE FG : Line) (α : Circle)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hd0ad : d0.onLine AD) (hdad0 : between d a d0)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α)
    (hecirc : e.onCircle α) (haAE : a.onLine AE) (heAE : e.onLine AE) (hega : between e g a)
    (hgFG : g.onLine FG) (hfFG : f.onLine FG) (hafb : between a f b)
    (hg0off : ¬ g0.onLine AB) (hperp_g : ∠ a:f:g0 = ∟) (hg0FG : g0.onLine FG)
    (hstep3 : ∠ d:a:e = ∟) (hstep2 : ∠ b:a:d < ∟)
    (hassump1 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α)
    (hassump2 : a.onLine AB ∧ b.onLine AB ∧ b.onCircle α) :
    ∠ d:a:b = ∠ a:e:b := by
  have hADtangent : ¬ AD.intersectsCircle α := hassump1.2
  have hbcirc : b.onCircle α := hassump2.2.2
  have step14_fgcirc : FG.intersectsCircle α := by euclid_apply (helper_3_33_step14_fgcirc g FG α (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)))
  have step14_edab : e.opposingSides d AB := by euclid_apply (helper_3_33_step14_edab a b d d0 e f g AB AD AE α (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show between e g a; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show ¬ AD.intersectsCircle α; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:d < ∟; assumption)))
  euclid_apply (intersections_circle_line α FG) as (c1, c2)
  by_cases hc1 : c1.opposingSides d0 AB
  · have step14_c1 : ∠ d:a:b = ∠ a:e:b := by euclid_apply (helper_3_33_step14_c1 a b d d0 e c1 AB AD α (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show c1.onCircle α; assumption)) (by euclid_assumption "" (show ¬ AD.intersectsCircle α; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ¬ e.onLine AB; assumption)) (by euclid_assumption "" (show ¬ d.onLine AB; assumption)) (by euclid_assumption "" (show ¬ e.sameSide d AB; assumption)) (by euclid_assumption "" (show c1.opposingSides d0 AB; assumption)))
    exact step14_c1
  · have step14_c2 : ∠ d:a:b = ∠ a:e:b := by euclid_apply (helper_3_33_step14_c2 a b d d0 e f g g0 c1 c2 AB AD FG α (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show c1.onCircle α; assumption)) (by euclid_assumption "" (show c2.onCircle α; assumption)) (by euclid_assumption "" (show c1.onLine FG; assumption)) (by euclid_assumption "" (show c2.onLine FG; assumption)) (by euclid_assumption "" (show c1 ≠ c2; assumption)) (by euclid_assumption "" (show ¬ g0.onLine AB; assumption)) (by euclid_assumption "" (show g0.onLine FG; assumption)) (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ¬ AD.intersectsCircle α; assumption)) (by euclid_assumption "" (show ¬ e.onLine AB; assumption)) (by euclid_assumption "" (show ¬ d.onLine AB; assumption)) (by euclid_assumption "" (show ¬ e.sameSide d AB; assumption)) (by euclid_assumption "" (show ¬ c1.opposingSides d0 AB; assumption)))
    exact step14_c2

end Elements.Book3
