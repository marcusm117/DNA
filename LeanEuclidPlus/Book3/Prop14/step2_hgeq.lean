import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Perpendicular-foot uniqueness (G side): the I.12 foot `hg` coincides with the given foot `g`.
theorem helper_3_14_step2_hgeq
    (c d e g hg : Point) (CD : Line)
    (h_e_off_CD : ¬ e.onLine CD)
    (hcCD : c.onLine CD) (hgCD : g.onLine CD) (hhgCD : hg.onLine CD)
    (hcgd : between c g d) (hgangle : ∠ c:g:e = ∟)
    (hperp : ∀ (p : Point), p.onLine CD → p ≠ hg → ∠ p:hg:e = ∟) :
    hg = g := by
  by_contra hne
  have h1 : ∠ g:hg:e = ∟ := hperp g hgCD (fun h => hne h.symm)
  euclid_apply (line_from_points e hg) as EHG
  euclid_apply (line_from_points e g) as EG2
  have h2 : ∠ e:g:hg = ∟ := by euclid_finish
  have htri : formTriangle e hg g EHG CD EG2 := by euclid_finish
  euclid_apply (Elements.Book1.proposition_17 e hg g EHG CD EG2)
  euclid_finish

end Elements.Book3
