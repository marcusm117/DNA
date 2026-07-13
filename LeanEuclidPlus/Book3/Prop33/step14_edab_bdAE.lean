import SystemE
import Book3.Prop33.step14_edab_bdAE_beAD
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- b and d are on the same side of AE (perpendicular to AD at a): b lies on the circle-side of the
-- tangent AD (same side as e), and ∠d:a:b < ∟ = ∠d:a:e. If b were on the far (d0) side of AE, ray ae
-- would be interior to ∠d:a:b, forcing ∠d:a:b ≥ ∠d:a:e = ∟, contradicting ∠b:a:d < ∟.
theorem helper_3_33_step14_edab_bdAE
    (a b d d0 e f : Point) (AD AE AB : Line) (α : Circle)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hadne : a ≠ d) (habne : a ≠ b)
    (hd0ad : d0.onLine AD) (hdad0 : between d a d0)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (heane : e ≠ a)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hADAEne : AD ≠ AE) (hafb : between a f b)
    (hacirc : a.onCircle α) (hbcirc : b.onCircle α) (hecirc : e.onCircle α)
    (hADtangent : ¬ AD.intersectsCircle α)
    (hstep3 : ∠ d:a:e = ∟) (hstep2 : ∠ b:a:d < ∟) :
    b.sameSide d AE := by
  have step14_edab_bdAE_beAD : b.sameSide e AD := by euclid_apply (helper_3_33_step14_edab_bdAE_beAD a b e f AD AE α (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show AD ≠ AE; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show a.onCircle α; assumption)) (by euclid_assumption "" (show b.onCircle α; assumption)) (by euclid_assumption "" (show e.onCircle α; assumption)) (by euclid_assumption "" (show ¬ AD.intersectsCircle α; assumption)))
  by_contra hns
  euclid_finish

end Elements.Book3
