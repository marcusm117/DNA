import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step20 (a b c d e f g : Point) (AB BC AC FC GB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcFC : c.onLine FC) (hfFC : f.onLine FC)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hbGB : b.onLine GB) (hgGB : g.onLine GB)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (habd : between a b d) (hbfd : between b f d)
    (hace : between a c e) (hage : between a g e)
    (hassump1 : ∠ a:b:g = ∠ a:c:f)
    (hassump2 : ∠ c:b:g = ∠ b:c:f)
    (h_step11 : |(b─f)| = |(c─g)|)
    (h_step11a1 : |(a─f)| = |(a─g)|)
    (h_step11a2 : |(a─b)| = |(a─c)|) :
    ∠ a:b:c = ∠ a:c:b := by
  have ha_ne_b : a ≠ b := (between_symm a b d habd).2.1
  have ha_ne_c : a ≠ c := (between_symm a c e hace).2.1
  have hb_ne_f : b ≠ f := (between_symm b f d hbfd).2.1
  have hg_ne_a : g ≠ a := (between_symm a g e hage).2.1.symm
  have h_bf_nn : 0 ≤ |(b─f)| := segment_gte_zero (b─f)
  have hgAC : g.onLine AC := by
    have heAC : e.onLine AC := between_same_line_out a c e AC ⟨hace, haAC, hcAC⟩
    exact between_same_line_in a g e AC ⟨hage, haAC, heAC⟩
  -- Derive between a b f
  have h_s1 := between_symm a b d habd
  have h_s2 := between_symm b f d hbfd
  have hd_f_a : between d f a := between_trans_in d b a f ⟨h_s1.1, h_s2.1⟩
  have ha_f_d : between a f d := (between_symm d f a hd_f_a).1
  have ha_ne_f : a ≠ f := (between_symm a f d ha_f_d).2.1
  have habf : between a b f := by
    rcases between_points a b f AB ⟨ha_ne_b, hb_ne_f, ha_ne_f.symm, haAB, hbAB, hfAB⟩
        with h | h | h
    · exact h
    · exact absurd (between_trans_out b a f d ⟨h, ha_f_d⟩) h_s1.2.2.2
    · exact absurd hbfd (between_not_trans a f b d ⟨h, ha_f_d⟩)
  -- Derive c ≠ g (metric: |bf| > 0 since b ≠ f)
  have hcg_ne : c ≠ g := by
    intro hcg
    have heq : |(a─c)| = |(a─g)| := by rw [hcg]
    have h1 : |(b─f)| ≤ 0 := by
      linarith [h_step11a1, h_step11a2, between_if a b f habf, heq]
    exact hb_ne_f (zero_segment_if b f (le_antisymm h1 h_bf_nn))
  -- Derive between a c g (c is between a and g)
  have hacg : between a c g := by
    rcases between_points a c g AC ⟨ha_ne_c, hcg_ne, hg_ne_a, haAC, hcAC, hgAC⟩
        with h | h | h
    · exact h
    · exact absurd (between_trans_out c a g e ⟨h, hage⟩) (between_symm a c e hace).2.2.2
    · exfalso
      have h_gc_nn : 0 ≤ |(g─c)| := segment_gte_zero (g─c)
      have h1 : |(b─f)| ≤ 0 := by
        linarith [h_step11a1, h_step11a2, between_if a b f habf, between_if a g c h, h_gc_nn]
      exact hb_ne_f (zero_segment_if b f (le_antisymm h1 h_bf_nn))
  -- Derive non-equality facts
  have hb_ne_g : b ≠ g := by
    intro hbg
    exact hACneAB (two_points_determine_line a b AC AB ⟨⟨haAC, hbg ▸ hgAC, ha_ne_b⟩, haAB, hbAB⟩)
  have hc_ne_f : c ≠ f := by
    intro hcf
    exact hACneAB (two_points_determine_line a c AC AB ⟨⟨haAC, hcAC, ha_ne_c⟩, haAB, hcf ▸ hfAB⟩)
  -- Derive ¬onLine conditions
  have hc_not_AB : ¬(c.onLine AB) := by
    intro hcAB
    exact hACneAB (two_points_determine_line a c AC AB ⟨⟨haAC, hcAC, ha_ne_c⟩, haAB, hcAB⟩)
  have hc_not_GB : ¬(c.onLine GB) := by
    intro hcGB
    have hGB_AC : GB = AC :=
      two_points_determine_line c g GB AC ⟨⟨hcGB, hgGB, hcg_ne⟩, hcAC, hgAC⟩
    exact hACneAB (two_points_determine_line a b AC AB ⟨⟨haAC, hGB_AC ▸ hbGB, ha_ne_b⟩, haAB, hbAB⟩)
  have hb_not_AC : ¬(b.onLine AC) := by
    intro hbAC
    exact hACneAB (two_points_determine_line a b AC AB ⟨⟨haAC, hbAC, ha_ne_b⟩, haAB, hbAB⟩)
  have hb_not_FC : ¬(b.onLine FC) := by
    intro hbFC
    have hAB_FC : AB = FC :=
      two_points_determine_line b f AB FC ⟨⟨hbAB, hfAB, hb_ne_f⟩, hbFC, hfFC⟩
    exact hACneAB (two_points_determine_line a c AC AB ⟨⟨haAC, hcAC, ha_ne_c⟩, haAB, hAB_FC ▸ hcFC⟩)
  -- Derive line distinctness
  have hAB_ne_GB : AB ≠ GB := by
    intro hABGB
    exact hACneAB (two_points_determine_line a g AC AB ⟨⟨haAC, hgAC, hg_ne_a.symm⟩, haAB, hABGB ▸ hgGB⟩)
  have hAC_ne_FC : AC ≠ FC := by
    intro hACFC
    exact hACneAB (two_points_determine_line a f AC AB ⟨⟨haAC, hACFC ▸ hfFC, ha_ne_f⟩, haAB, hfAB⟩)
  -- Derive sameSide conditions using Pasch
  have hgca : between g c a := (between_symm a c g hacg).1
  have ha_ss_c_GB : a.sameSide c GB :=
    same_side_symm c a GB (pasch_2 g c a GB ⟨hgca, hgGB, hc_not_GB⟩)
  have hg_ss_c_AB : g.sameSide c AB :=
    same_side_symm c g AB (pasch_2 a c g AB ⟨hacg, haAB, hc_not_AB⟩)
  have hfba : between f b a := (between_symm a b f habf).1
  have ha_ss_b_FC : a.sameSide b FC :=
    same_side_symm b a FC (pasch_2 f b a FC ⟨hfba, hfFC, hb_not_FC⟩)
  have hf_ss_b_AC : f.sameSide b AC :=
    same_side_symm b f AC (pasch_2 a b f AC ⟨habf, haAC, hb_not_AC⟩)
  -- Apply sum_angles_onlyif for angle decomposition at B and C
  have h_sum_abg : ∠ a:b:g = ∠ a:b:c + ∠ c:b:g :=
    sum_angles_onlyif b a g c AB GB
      ⟨hbAB, hbGB, haAB, hgGB, ha_ne_b.symm, hb_ne_g,
        hc_not_AB, hc_not_GB, hAB_ne_GB, ha_ss_c_GB, hg_ss_c_AB⟩
  have h_sum_acf : ∠ a:c:f = ∠ a:c:b + ∠ b:c:f :=
    sum_angles_onlyif c a f b AC FC
      ⟨hcAC, hcFC, haAC, hfFC, ha_ne_c.symm, hc_ne_f,
        hb_not_AC, hb_not_FC, hAC_ne_FC, ha_ss_b_FC, hf_ss_b_AC⟩
  linarith [h_sum_abg, h_sum_acf, hassump1, hassump2]

end Elements.Book1
