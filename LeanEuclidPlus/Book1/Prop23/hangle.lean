import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_23_hangle (a b f g : Point) (AB FA : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hg_AB : g.onLine AB)
    (ha_FA : a.onLine FA) (hf_FA : f.onLine FA)
    (hfoff : ¬f.onLine AB) (hfa : f ≠ a) (hab : a ≠ b)
    (hg_notbetween : ¬between g a b)
    (h_ag : |(a─g)| = |(c─e)|) (hce : c ≠ e)
    (hstep6 : ∠ d:c:e = ∠ f:a:g)
    : ∠ f:a:b = ∠ d:c:e := by
  have h_gne : g ≠ a := by euclid_finish
  euclid_apply (equal_angles a f f b g FA AB)
  euclid_finish

end Elements.Book1
