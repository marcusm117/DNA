import SystemE
import Book3.Prop33.step14_edab_bdAE
import Book3.Prop33.step14_edab_gbAD
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- e and d are on opposite sides of AB: e is in the alternate segment. g (centre) is on b's side of the
-- tangent AD (step14_edab_gbAD) and b is on d's side of the perpendicular AE (step14_edab_bdAE); by
-- triple_incidence_1 g and d are then on opposite sides of AB, and g.sameSide e AB (pasch_2) transfers
-- this to e.
theorem helper_3_33_step14_edab
    (a b d d0 e f g : Point) (AB AD AE : Line) (α : Circle)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hd0ad : d0.onLine AD) (hdad0 : between d a d0)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hega : between e g a)
    (hafb : between a f b)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α) (hbcirc : b.onCircle α) (hecirc : e.onCircle α)
    (hADtangent : ¬ AD.intersectsCircle α)
    (hstep3 : ∠ d:a:e = ∟) (hstep2 : ∠ b:a:d < ∟) :
    e.opposingSides d AB := by
  have hadne : a ≠ d := by euclid_finish
  have heane : e ≠ a := by euclid_finish
  have hgAE : g.onLine AE := by euclid_finish
  have hADAEne : AD ≠ AE := by euclid_finish
  have step14_edab_bdAE : b.sameSide d AE := by euclid_apply (helper_3_33_step14_edab_bdAE a b d d0 e f AD AE AB α (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d0.onLine AD; assumption)) (by euclid_assumption "" (show between d a d0; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AD ≠ AE; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show ¬ AD.intersectsCircle α; assumption)) (by euclid_assumption "" (show ∠ d:a:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:d < ∟; assumption)))
  have step14_edab_gbAD : g.sameSide b AD := by euclid_apply (helper_3_33_step14_edab_gbAD a b d f g AD α (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show g.isCentre α; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show ¬ AD.intersectsCircle α; assumption)))
  euclid_apply (triple_incidence_1 AE AB AD a g b d)
  euclid_apply (pasch_2 a g e AB)
  euclid_finish

end Elements.Book3
