import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_22_step7
    (k f g : Point) (KF KG : Line) (DKL KLH : Circle)
    (hkf_kf : k.onLine KF) (hf_kf : f.onLine KF)
    (hkg_kg : k.onLine KG) (hg_kg : g.onLine KG)
    (hkOnDKL : k.onCircle DKL) (hcenF : f.isCentre DKL)
    (hkOnKLH : k.onCircle KLH) (hcenG : g.isCentre KLH) :
    distinctPointsOnLine k f KF ∧ distinctPointsOnLine k g KG := by
  have hkf : k ≠ f := by
    intro heq
    have hfinside : f.insideCircle DKL := center_inside_circle f DKL hcenF
    exact inside_not_on_circle f DKL hfinside (heq ▸ hkOnDKL)
  have hkg : k ≠ g := by
    intro heq
    have hginside : g.insideCircle KLH := center_inside_circle g KLH hcenG
    exact inside_not_on_circle g KLH hginside (heq ▸ hkOnKLH)
  exact ⟨⟨hkf_kf, hf_kf, hkf⟩, ⟨hkg_kg, hg_kg, hkg⟩⟩

end Elements.Book1
