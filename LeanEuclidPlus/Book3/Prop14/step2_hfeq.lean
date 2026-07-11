import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Perpendicular-foot uniqueness (F side): the I.12 foot `hf` coincides with the given foot `f`.
-- Uses the STRENGTHENED I.12 output `hperp` (a right angle to EVERY point of AB), so the right
-- angle at hf toward f is immediate — no `a ≠ hf` needed.  If hf ≠ f, triangle E-hf-f would
-- have two right angles (at hf and at f), contradicting I.17.
theorem helper_3_14_step2_hfeq
    (a b e f hf : Point) (AB : Line)
    (h_e_off_AB : ¬ e.onLine AB)
    (haAB : a.onLine AB) (hfAB : f.onLine AB) (hhfAB : hf.onLine AB)
    (hafb : between a f b) (hfangle : ∠ a:f:e = ∟)
    (hperp : ∀ (p : Point), p.onLine AB → p ≠ hf → ∠ p:hf:e = ∟) :
    hf = f := by
  by_contra hne
  have h1 : ∠ f:hf:e = ∟ := hperp f hfAB (fun h => hne h.symm)
  euclid_apply (line_from_points e hf) as EHF
  euclid_apply (line_from_points e f) as EF2
  have h2 : ∠ e:f:hf = ∟ := by euclid_finish
  have htri : formTriangle e hf f EHF AB EF2 := by euclid_finish
  euclid_apply (Elements.Book1.proposition_17 e hf f EHF AB EF2)
  euclid_finish

end Elements.Book3
