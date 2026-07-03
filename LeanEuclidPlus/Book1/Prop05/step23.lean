import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step23 (a b c d e f g : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hstep15 : distinctPointsOnLine b c BC)
    (habd : between a b d) (hbfd : between b f d)
    (hace : between a c e) (hage : between a g e)
    (h_step11 : |(b─f)| = |(c─g)|)
    (h_step11a1 : |(a─f)| = |(a─g)|)
    (h_step11a2 : |(a─b)| = |(a─c)|) :
    (∠ f:b:c = ∠ c:b:d) ∧ (∠ g:c:b = ∠ b:c:e) := by
  -- Basic non-equalities from betweenness
  have hb_ne_f : b ≠ f := (between_symm b f d hbfd).2.1
  have hb_ne_d : b ≠ d := (between_symm b f d hbfd).2.2.1
  have hb_ne_c : b ≠ c := hstep15.2.2
  have ha_ne_c : a ≠ c := (between_symm a c e hace).2.1
  -- D is on line AB
  have hdAB : d.onLine AB := between_same_line_out a b d AB ⟨habd, haAB, hbAB⟩
  -- E is on line AC
  have heAC : e.onLine AC := between_same_line_out a c e AC ⟨hace, haAC, hcAC⟩
  -- G is on line AC
  have hgAC : g.onLine AC := between_same_line_in a g e AC ⟨hage, haAC, heAC⟩
  -- C ≠ G: if c=g then |b─f| = |c─c| = 0 → b=f, contradiction
  have hcg_ne : c ≠ g := by
    intro hcg
    have : |(b─f)| = 0 := (hcg ▸ h_step11).trans (zero_segment_onlyif g g rfl)
    exact hb_ne_f (zero_segment_if b f this)
  -- ¬ between f b d: from between_symm b f d
  have h_neg_fbd : ¬ between f b d := (between_symm b f d hbfd).2.2.2
  -- C ≠ E: from double between_symm
  have hc_ne_e : c ≠ e := ((between_symm e c a (between_symm a c e hace).1).2.1).symm
  -- G ≠ A: from between_symm
  have hg_ne_a : g ≠ a := (between_symm a g e hage).2.1.symm
  -- ¬ between g c e (metric: if g c e then 2*|c─g| = 0 → c = g)
  have h_neg_gce : ¬ between g c e := by
    intro h_gce
    have h_cg_nn : 0 ≤ |(c─g)| := segment_gte_zero (c─g)
    have hgc_sym : |(g─c)| = |(c─g)| := segment_symmetric g c
    have h1 : |(c─g)| ≤ 0 := by
      linarith [between_if g c e h_gce, between_if a c g
            (by rcases between_points a c g AC ⟨ha_ne_c, hcg_ne, hg_ne_a, haAC, hcAC, hgAC⟩
                    with h | h | h
                · exact h
                · exact absurd (between_trans_out c a g e ⟨h, hage⟩)
                                (between_symm a c e hace).2.2.2
                · exfalso
                  have h_gc_nn : 0 ≤ |(g─c)| := segment_gte_zero (g─c)
                  have habf : between a b f := by
                    have h_s1 := between_symm a b d habd
                    have h_s2 := between_symm b f d hbfd
                    have hd_f_a := between_trans_in d b a f ⟨h_s1.1, h_s2.1⟩
                    have ha_f_d := (between_symm d f a hd_f_a).1
                    have ha_ne_f := (between_symm a f d ha_f_d).2.1
                    have ha_ne_b := (between_symm a b d habd).2.1
                    rcases between_points a b f AB ⟨ha_ne_b, hb_ne_f, ha_ne_f.symm, haAB, hbAB, hfAB⟩
                        with hab | hab | hab
                    · exact hab
                    · exact absurd (between_trans_out b a f d ⟨hab, ha_f_d⟩) h_s1.2.2.2
                    · exact absurd hbfd (between_not_trans a f b d ⟨hab, ha_f_d⟩)
                  have h_bf_nn : 0 ≤ |(b─f)| := segment_gte_zero (b─f)
                  have : |(b─f)| ≤ 0 := by
                    linarith [h_step11a1, h_step11a2, between_if a b f habf, h_step11,
                               between_if a g c h, h_gc_nn]
                  exact hb_ne_f (zero_segment_if b f (le_antisymm this h_bf_nn))),
              between_if a g e hage, between_if a c e hace]
    exact hcg_ne (zero_segment_if c g (le_antisymm h1 h_cg_nn))
  -- Part 1: ∠ f:b:c = ∠ c:b:d via equal_angles (F and D on same ray from B)
  have hfbc_dbc : ∠ f:b:c = ∠ d:b:c :=
    equal_angles b f d c c AB BC
      ⟨hbAB, hfAB, hdAB, hbBC, hcBC, hcBC,
        hb_ne_f.symm, hb_ne_d.symm, hb_ne_c.symm, hb_ne_c.symm,
        h_neg_fbd, fun h => (between_symm c b c h).2.2.1 rfl⟩
  have part1 : ∠ f:b:c = ∠ c:b:d :=
    hfbc_dbc.trans (angle_symm d b c ⟨hb_ne_d.symm, hb_ne_c⟩)
  -- Part 2: ∠ g:c:b = ∠ b:c:e via equal_angles (G and E on same ray from C)
  have hgcb_ecb : ∠ g:c:b = ∠ e:c:b :=
    equal_angles c g e b b AC BC
      ⟨hcAC, hgAC, heAC, hcBC, hbBC, hbBC,
        hcg_ne.symm, hc_ne_e.symm, hb_ne_c, hb_ne_c,
        h_neg_gce, fun h => (between_symm b c b h).2.2.1 rfl⟩
  have part2 : ∠ g:c:b = ∠ b:c:e :=
    hgcb_ecb.trans (angle_symm e c b ⟨hc_ne_e.symm, hb_ne_c.symm⟩)
  exact ⟨part1, part2⟩

end Elements.Book1
