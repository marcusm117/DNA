import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step4 (a d f f0 : Point) (BCD AFG : Circle) (AE DF_line : Line)
    (ha_onAE : a.onLine AE) (hd_onBCD : d.onCircle BCD)
    (hd_onAE : d.onLine AE) (hf_onAFG : f.onCircle AFG)
    (hd_onDF : d.onLine DF_line) (hf_onDF : f.onLine DF_line) (hf0_onDF : f0.onLine DF_line)
    (hf0_off_AE : ¬f0.onLine AE) (hangle : ∠a:d:f0 = ∟)
    (hbetween_ade : between a d e) (hdfne : d ≠ f) (hdf0ne : d ≠ f0) :
    d.onCircle BCD ∧ d.onLine AE ∧ f.onCircle AFG ∧ ¬(f.onLine AE) ∧ ∠a:d:f = ∟ := by
  have ha_ne_d : a ≠ d := (between_symm a d e hbetween_ade).2.1
  have hf_off_AE : ¬f.onLine AE := by
    intro hf_AE
    exact hf0_off_AE ((two_points_determine_line d f AE DF_line
        ⟨⟨hd_onAE, hf_AE, hdfne⟩, hd_onDF, hf_onDF⟩) ▸ hf0_onDF)
  have ha_off_DF : ¬a.onLine DF_line := by
    intro ha_DF
    exact hf0_off_AE ((two_points_determine_line a d AE DF_line
        ⟨⟨ha_onAE, hd_onAE, ha_ne_d⟩, ha_DF, hd_onDF⟩) ▸ hf0_onDF)
  have hangle_adf : ∠a:d:f = ∟ := by
    by_cases hbet : between f d f0
    · -- f and f0 on opposite sides of d; perpendicular_onlyif gives supplement ∟
      have hbet_f0df : between f0 d f := (between_symm f d f0 hbet).1
      have hangle_f0da : ∠f0:d:a = ∟ :=
        (angle_symm f0 d a ⟨hdf0ne.symm, ha_ne_d.symm⟩).trans hangle
      exact (perpendicular_onlyif f0 f d a DF_line
          ⟨hf0_onDF, hf_onDF, hbet_f0df, ha_off_DF, hangle_f0da⟩).symm.trans hangle_f0da
    · -- f and f0 on same side of d; equal_angles gives ∠a:d:f = ∠a:d:f0
      have hna_da : ¬between a d a := fun h => absurd rfl (between_symm a d a h).2.2.1
      exact (equal_angles d a a f f0 AE DF_line
          ⟨hd_onAE, ha_onAE, ha_onAE, hd_onDF, hf_onDF, hf0_onDF,
           ha_ne_d, ha_ne_d, hdfne.symm, hdf0ne.symm, hna_da, hbet⟩).trans hangle
  exact ⟨hd_onBCD, hd_onAE, hf_onAFG, hf_off_AE, hangle_adf⟩

end Elements.Book3
