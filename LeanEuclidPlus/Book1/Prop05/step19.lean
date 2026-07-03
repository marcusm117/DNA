import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step19 (a b c d e f g : Point) (AB AC GB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbGB : b.onLine GB) (hgGB : g.onLine GB)
    (hACneAB : AC ≠ AB)
    (ha_ne_b : a ≠ b)
    (habd : between a b d) (hbfd : between b f d)
    (hace : between a c e) (hage : between a g e)
    (hstep15 : distinctPointsOnLine b c BC)
    (h_step17 : (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c)) :
    ∠ b:c:f = ∠ c:b:g := by
  have hbc : b ≠ c := hstep15.2.2
  have h_s1 := between_symm a b d habd
  have h_s2 := between_symm b f d hbfd
  have hd_f_a : between d f a := between_trans_in d b a f ⟨h_s1.1, h_s2.1⟩
  have ha_f_d : between a f d := (between_symm d f a hd_f_a).1
  have ha_ne_f : a ≠ f := (between_symm a f d ha_f_d).2.1
  have hc_ne_f : c ≠ f := by
    intro hcf
    exact hACneAB
      (two_points_determine_line a c AC AB
        ⟨⟨haAC, hcAC, (between_symm a c e hace).2.1⟩, haAB, hcf ▸ hfAB⟩)
  have hgAC : g.onLine AC := by
    have heAC : e.onLine AC := between_same_line_out a c e AC ⟨hace, haAC, hcAC⟩
    exact between_same_line_in a g e AC ⟨hage, haAC, heAC⟩
  have hb_ne_g : b ≠ g := by
    intro hbg
    exact hACneAB
      (two_points_determine_line a b AC AB ⟨⟨haAC, hbg ▸ hgAC, ha_ne_b⟩, haAB, hbAB⟩)
  have h1 : ∠ b:c:f = ∠ f:c:b := angle_symm b c f ⟨hbc, hc_ne_f⟩
  have h2 : ∠ c:b:g = ∠ g:b:c := angle_symm c b g ⟨hbc.symm, hb_ne_g⟩
  exact h1.trans (h_step17.2.trans h2.symm)

end Elements.Book1
