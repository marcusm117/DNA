import SystemE
import Book.Prop04
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step7 (a b c d e f g : Point) (AB BC AC FC GB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABne : AB ≠ BC) (hBCne : BC ≠ AC) (hACne : AC ≠ AB)
    (hcFC : c.onLine FC) (hfFC : f.onLine FC) (hfAB : f.onLine AB)
    (hbGB : b.onLine GB) (hgGB : g.onLine GB)
    (habd : between a b d) (hbfd : between b f d)
    (hage : between a g e) (hace : between a c e)
    (h_step4 : |(f─a)| = |(g─a)| ∧ |(a─c)| = |(a─b)|)
    (h_step5 : ∠f:a:c = ∠f:a:g ∧ ∠g:a:b = ∠f:a:g)
    (h_step6 : |(f─c)| = |(g─b)|) :
    Triangle.area △ a:f:c = Triangle.area △ a:g:b := by
  obtain ⟨h_fa_ga, h_ac_ab⟩ := h_step4
  obtain ⟨h_fac_fag, h_gab_fag⟩ := h_step5
  euclid_apply (proposition_4 a f c a g b AB FC AC AC GB AB)
  euclid_apply (area_congruence a f c a g b)
  euclid_finish

end Elements.Book1
