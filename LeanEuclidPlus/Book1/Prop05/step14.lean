import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step14 (a b c d e f g : Point) (AB AC FC GB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcFC : c.onLine FC) (hfFC : f.onLine FC)
    (hbGB : b.onLine GB) (hgGB : g.onLine GB)
    (hACneAB : AC ≠ AB)
    (habd : between a b d) (hbfd : between b f d)
    (hace : between a c e) (hage : between a g e)
    (haf_ag : |(a─f)| = |(a─g)|)
    (hab_ac : |(a─b)| = |(a─c)|)
    (h_step10 : ∠a:f:c = ∠a:g:b) :
    ∠ b:f:c = ∠ c:g:b := by
  -- Derive between a b f (A,B,F order) from between a b d ∧ between b f d
  have h_s1 := between_symm a b d habd
  have h_s2 := between_symm b f d hbfd
  have hb_ne_f : b ≠ f := h_s2.2.1
  have ha_ne_b : a ≠ b := h_s1.2.1
  have hd_f_a : between d f a := between_trans_in d b a f ⟨h_s1.1, h_s2.1⟩
  have ha_f_d : between a f d := (between_symm d f a hd_f_a).1
  have ha_ne_f : a ≠ f := (between_symm a f d ha_f_d).2.1
  have habf : between a b f := by
    rcases between_points a b f AB ⟨ha_ne_b, hb_ne_f, ha_ne_f.symm, haAB, hbAB, hfAB⟩
        with h | h | h
    · exact h
    · exact absurd (between_trans_out b a f d ⟨h, ha_f_d⟩) h_s1.2.2.2
    · exact absurd hbfd (between_not_trans a f b d ⟨h, ha_f_d⟩)
  -- Conditions for equal_angles f b a c c AB FC (∠b:f:c = ∠a:f:c)
  -- ¬between b f a: if between b f a then between_trans_out a b f a gives between a b a → a≠a
  have h_neg_bfa : ¬ between b f a :=
    fun h => (between_symm a b a (between_trans_out a b f a ⟨habf, h⟩)).2.2.1 rfl
  -- c ≠ f: if c=f then f on AC, and a,f on both AB∧AC with a≠f → AB=AC. Contradiction.
  have ha_ne_c : a ≠ c := (between_symm a c e hace).2.1
  have hc_ne_f : c ≠ f := by
    intro hcf
    exact hACneAB
      (two_points_determine_line a c AC AB ⟨⟨haAC, hcAC, ha_ne_c⟩, haAB, hcf ▸ hfAB⟩)
  -- Apply equal_angles: ∠b:f:c = ∠a:f:c
  have hbfc_afc : ∠b:f:c = ∠a:f:c :=
    equal_angles f b a c c AB FC
      ⟨hfAB, hbAB, haAB, hfFC, hcFC, hcFC, hb_ne_f, ha_ne_f, hc_ne_f, hc_ne_f,
        h_neg_bfa, fun h => (between_symm c f c h).2.2.1 rfl⟩
  -- Derive g.onLine AC and between a c g
  have heAC : e.onLine AC := between_same_line_out a c e AC ⟨hace, haAC, hcAC⟩
  have hgAC : g.onLine AC := between_same_line_in a g e AC ⟨hage, haAC, heAC⟩
  have h_bf_eq := between_if a b f habf
  have h_bf_nn : 0 ≤ |(b─f)| := segment_gte_zero (b─f)
  have hg_ne_a : g ≠ a := (between_symm a g e hage).2.1.symm
  have ha_ne_g : a ≠ g := hg_ne_a.symm
  have hc_ne_g : c ≠ g := by
    intro hcg
    have h1 : |(b─f)| ≤ 0 := by
      have heq : |(a─c)| = |(a─g)| := by rw [hcg]
      linarith [haf_ag, hab_ac, h_bf_eq, heq]
    exact hb_ne_f (zero_segment_if b f (le_antisymm h1 h_bf_nn))
  have hacg : between a c g := by
    rcases between_points a c g AC ⟨ha_ne_c, hc_ne_g, hg_ne_a, haAC, hcAC, hgAC⟩
        with h | h | h
    · exact h
    · exact absurd (between_trans_out c a g e ⟨h, hage⟩) (between_symm a c e hace).2.2.2
    · exfalso
      have h_gc_nn : 0 ≤ |(g─c)| := segment_gte_zero (g─c)
      have h1 : |(b─f)| ≤ 0 :=
        by linarith [haf_ag, hab_ac, h_bf_eq, between_if a g c h, h_gc_nn]
      exact hb_ne_f (zero_segment_if b f (le_antisymm h1 h_bf_nn))
  -- ¬between a g c: from between a c g, if between a g c then between_trans_in gives between a g g → g≠g
  have h_neg_agc : ¬ between a g c :=
    fun h =>
      (between_symm g g a (between_symm a g g (between_trans_in a c g g ⟨hacg, h⟩)).1).2.1 rfl
  -- b ≠ g: if b=g then b on AC, and a,b on both AB∧AC with a≠b → AB=AC. Contradiction.
  have hb_ne_g : b ≠ g := by
    intro hbg
    exact hACneAB
      (two_points_determine_line a b AC AB ⟨⟨haAC, hbg ▸ hgAC, ha_ne_b⟩, haAB, hbAB⟩)
  -- Apply equal_angles: ∠a:g:b = ∠c:g:b
  have hagb_cgb : ∠a:g:b = ∠c:g:b :=
    equal_angles g a c b b AC GB
      ⟨hgAC, haAC, hcAC, hgGB, hbGB, hbGB, ha_ne_g, hc_ne_g, hb_ne_g, hb_ne_g,
        h_neg_agc, fun h => (between_symm b g b h).2.2.1 rfl⟩
  -- Chain: ∠b:f:c = ∠a:f:c = ∠a:g:b = ∠c:g:b
  exact hbfc_afc.trans (h_step10.trans hagb_cgb)

end Elements.Book1
