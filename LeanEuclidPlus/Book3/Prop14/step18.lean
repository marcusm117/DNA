import SystemE
import Book3.Prop03.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Same construction as steps 4–7: III.3 bisects both chords, so |AB| = 2·|AF|, |CD| = 2·|CG|.
theorem helper_3_14_step18
    (a b c d e f g : Point) (ABDC : Circle) (AB CD EF EG : Line)
    (ha : a.onCircle ABDC) (hb : b.onCircle ABDC)
    (hc : c.onCircle ABDC) (hd : d.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab_ne : a ≠ b) (hfAB : f.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hcd_ne : c ≠ d) (hgCD : g.onLine CD)
    (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (heEG : e.onLine EG) (hgEG : g.onLine EG)
    (hafb : between a f b) (hcgd : between c g d)
    (hef : e ≠ f) (heg : e ≠ g)
    (hfangle : ∠ a:f:e = ∟) (hgangle : ∠ c:g:e = ∟) :
    |(a─b)| = |(a─f)| + |(a─f)| ∧ |(c─d)| = |(c─g)| + |(c─g)| := by
  refine ⟨?_, ?_⟩
  · have h_e_off : ¬ e.onLine AB := by euclid_finish
    euclid_apply (proposition_3 a b e f ABDC AB EF)
    have hbis : |(a─f)| = |(f─b)| := by euclid_finish
    have hsum : |(a─f)| + |(f─b)| = |(a─b)| := between_if a f b hafb
    linarith
  · have h_e_off2 : ¬ e.onLine CD := by euclid_finish
    euclid_apply (proposition_3 c d e g ABDC CD EG)
    have hbis2 : |(c─g)| = |(g─d)| := by euclid_finish
    have hsum2 : |(c─g)| + |(g─d)| = |(c─d)| := between_if c g d hcgd
    linarith

end Elements.Book3
