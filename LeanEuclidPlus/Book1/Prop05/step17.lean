import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step17 (a b c d e f g : Point) (AB BC AC FC GB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcFC : c.onLine FC) (hfFC : f.onLine FC)
    (hbGB : b.onLine GB) (hgGB : g.onLine GB)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (habd : between a b d) (hbfd : between b f d)
    (hace : between a c e) (hage : between a g e)
    (h_step13 : (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|))
    (h_step14 : ∠b:f:c = ∠c:g:b) :
    (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c) := by
  obtain ⟨h_bf_cg, h_fc_gb⟩ := h_step13
  have hgAC : g.onLine AC := by
    have heAC : e.onLine AC := between_same_line_out a c e AC ⟨hace, haAC, hcAC⟩
    exact between_same_line_in a g e AC ⟨hage, haAC, heAC⟩
  euclid_apply (proposition_4 f b c g c b AB BC FC AC BC GB)
  constructor <;> euclid_finish

end Elements.Book1
