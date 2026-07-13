import SystemE
import Book3.Prop16.Main
import Book3.Prop33.step38_hperp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- AD touches circle α (Prop 3.16 corr.): AE is a diameter (its far end e = antipode of a, through
-- centre g), and AD ⊥ AE at the extremity a (∠d:a:e0 = ∟ with e0 on AE ⟹ ∠d:a:e = ∟).  Apply
-- proposition_16 with touch a, opposite end e, centre g, tangent point d.
theorem helper_3_33_step38
    (a d e0 g : Point) (AD AE : Line) (α : Circle)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hadd : d ≠ a) (he0offAD : ¬ e0.onLine AD)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (hgAE : g.onLine AE)
    (hassump1 : ∠ d:a:e0 = ∟)   -- "$AD$ is at right-angles to the diameter $AE$, at its extremity"
    : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α := by
  euclid_apply (intersection_circle_line_extending_points α AE g a) as e
  have he_ne : e ≠ a := by euclid_finish
  have step38_hperp : ∠ d:a:e = ∟ := by euclid_apply (helper_3_33_step38_hperp a d e e0 AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)))
  euclid_apply (proposition_16 a e g d α AD)
  euclid_finish

end Elements.Book3
