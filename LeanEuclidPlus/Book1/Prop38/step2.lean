import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_38_step2
  (a b g : Point) (AD BF BG AC AB : Line)
  (ha_AD : a.onLine AD) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
  (hAB_BF : AB ≠ BF)
  (hb_BG : b.onLine BG) (hg_BG : g.onLine BG)
  (hg_AD : g.onLine AD) (hb_BF : b.onLine BF)
  (hAD_BF : ¬AD.intersectsLine BF)
  (hBG_AC : ¬BG.intersectsLine AC)
  : distinctPointsOnLine b g BG ∧ ¬BG.intersectsLine AC := by
  refine ⟨⟨hb_BG, hg_BG, ?_⟩, hBG_AC⟩
  euclid_finish

end Elements.Book1
