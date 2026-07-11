import SystemE
import Book3.Prop03.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Same as steps 4–6, applied to the chord CD: III.3 bisects it, so |CD| = 2·|CG|.
theorem helper_3_14_step7
    (c d e g : Point) (ABDC : Circle) (CD EG : Line)
    (hc : c.onCircle ABDC) (hd : d.onCircle ABDC)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hcd_ne : c ≠ d)
    (hcen : e.isCentre ABDC)
    (heEG : e.onLine EG) (hgEG : g.onLine EG)
    (hgCD : g.onLine CD) (hcgd : between c g d) (heg : e ≠ g)
    (hgangle : ∠ c:g:e = ∟) :
    |(c─d)| = |(c─g)| + |(c─g)| := by
  have h_e_off : ¬ e.onLine CD := by euclid_finish
  euclid_apply (proposition_3 c d e g ABDC CD EG)
  have hbis : |(c─g)| = |(g─d)| := by euclid_finish
  have hsum : |(c─g)| + |(g─d)| = |(c─d)| := between_if c g d hcgd
  linarith

end Elements.Book3
