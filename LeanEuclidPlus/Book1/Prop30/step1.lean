import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step1
    (AB CD EF GK : Line) (g h k : Point)
    (hg_AB : g.onLine AB) (hg_GK : g.onLine GK)
    (hh_EF : h.onLine EF) (hh_GK : h.onLine GK)
    (hk_CD : k.onLine CD) (hk_GK : k.onLine GK)
    (hEF_ne_AB : EF ≠ AB) (hCD_ne_EF : CD ≠ EF)
    (h_nopar_AB : ¬AB.intersectsLine EF) (h_nopar_CD : ¬CD.intersectsLine EF)
    : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  have hAB_ne_EF : AB ≠ EF := hEF_ne_AB.symm
  -- AB ≠ GK: if AB = GK then h (on GK and EF) → AB.intersectsLine EF, contradiction
  have hAB_ne_GK : AB ≠ GK := by
    intro heq
    have hh_AB : h.onLine AB := heq ▸ hh_GK
    euclid_apply (intersection_lines_common_point h AB EF)
    exact h_nopar_AB (by assumption)
  -- EF ≠ GK: if EF = GK then g (on GK and AB) → AB.intersectsLine EF, contradiction
  have hEF_ne_GK : EF ≠ GK := by
    intro heq
    have hg_EF : g.onLine EF := heq ▸ hg_GK
    euclid_apply (intersection_lines_common_point g AB EF)
    exact h_nopar_AB (by assumption)
  -- CD ≠ GK: if CD = GK then h (on GK and EF) → CD.intersectsLine EF, contradiction
  have hCD_ne_GK : CD ≠ GK := by
    intro heq
    have hh_CD : h.onLine CD := heq ▸ hh_GK
    euclid_apply (intersection_lines_common_point h CD EF)
    exact h_nopar_CD (by assumption)
  refine ⟨?_, ?_, ?_⟩
  · euclid_apply (intersection_lines_common_point g AB GK); assumption
  · euclid_apply (intersection_lines_common_point h EF GK); assumption
  · euclid_apply (intersection_lines_common_point k CD GK); assumption

end Elements.Book1
