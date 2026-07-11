import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop13.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_16_hgDG_foot_inr_dag
    (a a' d g : Point) (FA AE DG_line : Line) (e b : Point)
    (hFAon : a.onLine FA)
    (ha'FA : a'.onLine FA)
    (ha'ne : a ≠ a')
    (hd_off : ¬d.onLine FA)
    (hFAne : FA ≠ AE)
    (left_3 : between a d b)
    (right_4 : ∠ e:a:b = ∟)
    (left_5 : a.onLine AE)
    (left_6 : e.onLine AE)
    (right_6 : a ≠ e)
    (hDGd : d.onLine DG_line)
    (hDGg : g.onLine DG_line)
    (h : ∠ a':g:d = ∟)
    (hag : a = g)
    : ∠ a:g:d = ∟ := by
  subst hag
  -- After subst: hDGg : a.onLine DG_line, h : ∠a':a:d = ∟
  exfalso
  have hb_DG : b.onLine DG_line :=
    between_same_line_out a d b DG_line ⟨left_3, hDGg, hDGd⟩
  have hbsymm := between_symm a d b left_3
  have h_ane_d : a ≠ d := hbsymm.2.1
  have h_bne_a : b ≠ a := hbsymm.2.2.1.symm
  -- ∠e:a:d = ∟ via equal_angles (b and d both on DG_line, e on AE)
  have h_ead : ∠ e:a:d = ∟ := by
    euclid_apply (equal_angles a e e d b AE DG_line)
    linarith
  -- Collinear case 1: between a' a e → between_same_line_out → e on FA → FA=AE
  by_cases hbet1 : between a' a e
  · exact hFAne (two_points_determine_line a e FA AE
      ⟨⟨hFAon, between_same_line_out a' a e FA ⟨hbet1, ha'FA, hFAon⟩, right_6⟩, left_5, left_6⟩)
  -- Collinear case 2: between a' e a → between_same_line_in → e on FA → FA=AE
  by_cases hbet2 : between a' e a
  · exact hFAne (two_points_determine_line a e FA AE
      ⟨⟨hFAon, between_same_line_in a' e a FA ⟨hbet2, ha'FA, hFAon⟩, right_6⟩, left_5, left_6⟩)
  -- Collinear case 3: between a a' e → between_same_line_out → e on FA → FA=AE
  by_cases hbet3 : between a a' e
  · exact hFAne (two_points_determine_line a e FA AE
      ⟨⟨hFAon, between_same_line_out a a' e FA ⟨hbet3, hFAon, ha'FA⟩, right_6⟩, left_5, left_6⟩)
  -- Non-collinear case: a', a, e not collinear; derive contradiction from two perpendiculars
  -- Off-line facts
  have he_off_FA : ¬e.onLine FA := fun heFA =>
    hFAne (two_points_determine_line a e FA AE ⟨⟨hFAon, heFA, right_6⟩, left_5, left_6⟩)
  have ha'_off_AE : ¬a'.onLine AE := fun ha'AE =>
    hFAne (two_points_determine_line a a' FA AE ⟨⟨hFAon, ha'FA, ha'ne⟩, left_5, ha'AE⟩)
  have ha'_off_DG : ¬a'.onLine DG_line := fun ha'DG =>
    hd_off (two_points_determine_line a a' DG_line FA
      ⟨⟨hDGg, ha'DG, ha'ne⟩, hFAon, ha'FA⟩ ▸ hDGd)
  have hd_off_AE : ¬d.onLine AE := by
    intro hdAE
    have : AE = DG_line :=
      two_points_determine_line a d AE DG_line ⟨⟨left_5, hdAE, h_ane_d⟩, hDGg, hDGd⟩
    -- e, a, d collinear on DG_line: ∠e:a:d = ∟ is impossible
    have he_on_DG : e.onLine DG_line := this ▸ left_6
    euclid_finish
  have he_off_DG : ¬e.onLine DG_line := by
    intro heDG
    have : AE = DG_line :=
      two_points_determine_line a e AE DG_line ⟨⟨left_5, left_6, right_6⟩, hDGg, heDG⟩
    -- e, a, d collinear on DG_line: ∠e:a:d = ∟ is impossible
    euclid_finish
  have hFA_ne_DG : FA ≠ DG_line := fun hEq => ha'_off_DG (hEq ▸ ha'FA)
  have hAE_ne_DG : AE ≠ DG_line := fun hEq => he_off_DG (hEq ▸ left_6)
  have hb_off_AE : ¬b.onLine AE := by
    intro hbAE
    have : AE = DG_line :=
      two_points_determine_line a b AE DG_line ⟨⟨left_5, hbAE, h_bne_a.symm⟩, hDGg, hb_DG⟩
    exact he_off_DG (this ▸ left_6)
  -- Extend a'' on DG_line past a (beyond d): gives between d a a''
  obtain ⟨a'', ha''_DG, hbet_daa''⟩ := extend_point DG_line d a ⟨hDGd, hDGg, h_ane_d.symm⟩
  -- Distinctness from betweenness: apply between_symm twice to extract a≠a'' and a≠a'''
  have hbet_a''ad : between a'' a d := (between_symm d a a'' hbet_daa'').1
  have ha''_ne_a : a ≠ a'' := ((between_symm a'' a d hbet_a''ad).2.1).symm
  have ha''_ne_d : a'' ≠ d := (between_symm d a a'' hbet_daa'').2.2.1.symm
  have ha''_off_FA : ¬a''.onLine FA := fun ha''FA =>
    hd_off (two_points_determine_line a a'' DG_line FA
      ⟨⟨hDGg, ha''_DG, ha''_ne_a⟩, hFAon, ha''FA⟩ ▸ hDGd)
  have ha''_off_AE : ¬a''.onLine AE := fun ha''AE =>
    he_off_DG (two_points_determine_line a a'' AE DG_line
      ⟨⟨left_5, ha''AE, ha''_ne_a⟩, hDGg, ha''_DG⟩ ▸ left_6)
  -- Extend a''' on FA past a (beyond a'): gives between a' a a'''
  obtain ⟨a''', ha'''_FA, hbet_a'aa'''⟩ := extend_point FA a' a ⟨ha'FA, hFAon, ha'ne.symm⟩
  have hbet_a'''aa' : between a''' a a' := (between_symm a' a a''' hbet_a'aa''').1
  have ha'''_ne_a : a ≠ a''' := ((between_symm a''' a a' hbet_a'''aa').2.1).symm
  have ha'_ne_a''' : a' ≠ a''' := (between_symm a' a a''' hbet_a'aa''').2.2.1
  have ha'''_off_DG : ¬a'''.onLine DG_line := fun ha'''DG =>
    hd_off (two_points_determine_line a a''' DG_line FA
      ⟨⟨hDGg, ha'''DG, ha'''_ne_a⟩, hFAon, ha'''_FA⟩ ▸ hDGd)
  have ha'''_off_AE : ¬a'''.onLine AE := fun ha'''AE =>
    hFAne (two_points_determine_line a a''' FA AE ⟨⟨hFAon, ha'''_FA, ha'''_ne_a⟩, left_5, ha'''AE⟩)
  -- Proposition 13 applied four times at vertex a
  -- Distinctness helpers for distinctPointsOnLine (needs the first ≠ second form)
  have ha'_ne_a : a' ≠ a := ha'ne.symm
  have ha''_ne_a_sym : a'' ≠ a := ha''_ne_a.symm
  have ha'''_ne_a_sym : a''' ≠ a := ha'''_ne_a.symm
  -- (1) FA stands on DG_line at a: ∠a'':a:a' + ∠a':a:d = 2R
  have hprop13_1 : ∠ a'':a:a' + ∠ a':a:d = ∟+∟ :=
    Elements.Book1.proposition_13 a' a a'' d FA DG_line
      ⟨hFA_ne_DG, ⟨ha'FA, hFAon, ha'_ne_a⟩, ⟨ha''_DG, hDGd, ha''_ne_d⟩, hbet_daa''⟩
  have h_a''a' : ∠ a'':a:a' = ∟ := by linarith
  -- (2) AE stands on DG_line at a: ∠a'':a:e + ∠e:a:d = 2R
  have hprop13_2 : ∠ a'':a:e + ∠ e:a:d = ∟+∟ :=
    Elements.Book1.proposition_13 e a a'' d AE DG_line
      ⟨hAE_ne_DG, ⟨left_6, left_5, right_6.symm⟩, ⟨ha''_DG, hDGd, ha''_ne_d⟩, hbet_daa''⟩
  have h_a''e : ∠ a'':a:e = ∟ := by linarith
  -- (3) DG_line stands on FA at a: ∠a':a:a'' + ∠a'':a:a''' = 2R
  have hprop13_3 : ∠ a':a:a'' + ∠ a'':a:a''' = ∟+∟ :=
    Elements.Book1.proposition_13 a'' a a' a''' DG_line FA
      ⟨hFA_ne_DG.symm, ⟨ha''_DG, hDGg, ha''_ne_a_sym⟩, ⟨ha'FA, ha'''_FA, ha'_ne_a'''⟩, hbet_a'''aa'⟩
  -- angle_symm a b c needs: (a≠b) ∧ (b≠c); returns ∠a:b:c = ∠c:b:a (vertex b)
  have h_a'a'' : ∠ a':a:a'' = ∟ := by
    have := angle_symm a'' a a' ⟨ha''_ne_a_sym, ha'ne⟩; linarith
  have h_a''a''' : ∠ a'':a:a''' = ∟ := by linarith
  -- (4) FA stands on DG_line at a with a''': ∠a'':a:a''' + ∠a''':a:d = 2R
  have hprop13_4 : ∠ a'':a:a''' + ∠ a''':a:d = ∟+∟ :=
    Elements.Book1.proposition_13 a''' a a'' d FA DG_line
      ⟨hFA_ne_DG, ⟨ha'''_FA, hFAon, ha'''_ne_a_sym⟩, ⟨ha''_DG, hDGd, ha''_ne_d⟩, hbet_daa''⟩
  have h_a'''d : ∠ a''':a:d = ∟ := by linarith
  -- angle_symm variants (all: vertex = a; pair = (first≠a) ∧ (a≠last))
  have h_ea'' : ∠ e:a:a'' = ∟ := by
    have := angle_symm a'' a e ⟨ha''_ne_a_sym, right_6⟩; linarith
  have h_a'''a'' : ∠ a''':a:a'' = ∟ := by
    have := angle_symm a'' a a''' ⟨ha''_ne_a_sym, ha'''_ne_a⟩; linarith
  have h_dae : ∠ d:a:e = ∟ := by
    have := angle_symm e a d ⟨right_6.symm, h_ane_d⟩; linarith
  -- pasch_3: d and a'' on opposite sides of FA
  have hnot_d_ss_a''_FA : ¬d.sameSide a'' FA :=
    pasch_3 d a a'' FA ⟨hbet_daa'', hFAon⟩
  -- pasch_3: a' and a''' on opposite sides of DG_line
  have hnot_a'_ss_a'''_DG : ¬a'.sameSide a''' DG_line :=
    pasch_3 a' a a''' DG_line ⟨hbet_a'aa''', hDGg⟩
  -- pasch_3: a' and a''' on opposite sides of AE
  have hnot_a'_ss_a'''_AE : ¬a'.sameSide a''' AE :=
    pasch_3 a' a a''' AE ⟨hbet_a'aa''', left_5⟩
  -- pasch_2: d and b on same side of AE
  have hd_ss_b_AE : d.sameSide b AE := pasch_2 a d b AE ⟨left_3, left_5, hd_off_AE⟩
  -- Helper to transfer e on FA → contradiction
  have e_on_FA_absurd : e.onLine FA → False := fun heFA =>
    hFAne (two_points_determine_line a e FA AE ⟨⟨hFAon, heFA, right_6⟩, left_5, left_6⟩)
  -- Main case split: e on same side of FA as d, or opposite
  by_cases he_ss_d : e.sameSide d FA
  · -- Case A: e.sameSide d FA
    -- Need a'.sameSide d AE for sum_angles_onlyif a a' e d FA AE
    by_cases ha'_ss_d_AE : a'.sameSide d AE
    · -- Case A1: a'.sameSide d AE
      -- sum_angles_onlyif → ∠a':a:e = ∠a':a:d + ∠d:a:e = ∟+∟
      have hsum := sum_angles_onlyif a a' e d FA AE
        ⟨hFAon, left_5, ha'FA, left_6, ha'ne, right_6, hd_off, hd_off_AE, hFAne,
         ha'_ss_d_AE, he_ss_d⟩
      -- hsum : ∠a':a:e = ∠a':a:d + ∠d:a:e = ∟+∟
      exact hbet1 (flat_angle_if a' a e ⟨ha'ne.symm, right_6, by linarith⟩)
    · -- Case A2: ¬a'.sameSide d AE → use a''' (opposite arm on FA)
      -- pigeon_hole on AE: a', d, a''' all off AE
      have hpig_AE := same_side_pigeon_hole a' d a''' AE
        ⟨ha'_off_AE, hd_off_AE, ha'''_off_AE⟩
      -- Eliminate: ¬a'.sameSide d AE (case A2) AND ¬a'.sameSide a''' AE (pasch_3)
      have hd_ss_a'''_AE : d.sameSide a''' AE := by
        rcases hpig_AE with h1 | h2 | h3
        · exact absurd h1 ha'_ss_d_AE
        · exact absurd h2 hnot_a'_ss_a'''_AE
        · exact h3
      have ha'''_ss_d_AE : a'''.sameSide d AE := same_side_symm d a''' AE hd_ss_a'''_AE
      -- sum_angles_onlyif a a''' e d FA AE → ∠a''':a:e = ∠a''':a:d + ∠d:a:e = ∟+∟
      have hsum := sum_angles_onlyif a a''' e d FA AE
        ⟨hFAon, left_5, ha'''_FA, left_6, ha'''_ne_a, right_6, hd_off, hd_off_AE, hFAne,
         ha'''_ss_d_AE, he_ss_d⟩
      -- hsum : ∠a''':a:e = ∠a''':a:d + ∠d:a:e = ∟+∟
      have hflt : between a''' a e :=
        flat_angle_if a''' a e ⟨ha'''_ne_a.symm, right_6, by linarith⟩
      -- between a''' a e, a''' and a on FA → e on FA
      exact e_on_FA_absurd (between_same_line_out a''' a e FA ⟨hflt, ha'''_FA, hFAon⟩)
  · -- Case B: ¬e.sameSide d FA
    -- pigeon_hole on FA: e, d, a'' all off FA
    have hpig_FA := same_side_pigeon_hole e d a'' FA
      ⟨he_off_FA, hd_off, ha''_off_FA⟩
    -- Eliminate: ¬e.sameSide d FA (case B) AND ¬d.sameSide a'' FA (pasch_3)
    have he_ss_a''_FA : e.sameSide a'' FA := by
      rcases hpig_FA with h1 | h2 | h3
      · exact absurd h1 he_ss_d
      · exact h2
      · exact absurd h3 hnot_d_ss_a''_FA
    have ha''_ss_e_FA : a''.sameSide e FA := same_side_symm e a'' FA he_ss_a''_FA
    -- Case split on a'.sameSide e DG_line
    by_cases ha'_ss_e_DG : a'.sameSide e DG_line
    · -- Case B-α: a'.sameSide e DG_line
      -- sum_angles_onlyif a a' a'' e FA DG_line → ∠a':a:a'' = ∠a':a:e + ∠e:a:a''
      have hsum := sum_angles_onlyif a a' a'' e FA DG_line
        ⟨hFAon, hDGg, ha'FA, ha''_DG, ha'ne, ha''_ne_a, he_off_FA, he_off_DG,
         hFA_ne_DG, ha'_ss_e_DG, ha''_ss_e_FA⟩
      -- hsum : ∠a':a:a'' = ∠a':a:e + ∠e:a:a'' = ∠a':a:e + ∟
      -- ∠a':a:a'' = ∟ → ∠a':a:e = 0 → e on FA
      have hzero : ∠ a':a:e = 0 := by linarith
      exact e_on_FA_absurd
        (degenerated_angle_onlyif a a' e FA ⟨ha'ne, right_6, hFAon, ha'FA, hzero⟩).1
    · -- Case B-¬α: ¬a'.sameSide e DG_line
      -- pigeon_hole on DG_line: a', e, a''' all off DG_line
      -- gives a'.sameSide e ∨ a'.sameSide a''' ∨ e.sameSide a''' on DG_line
      have hpig_DG := same_side_pigeon_hole a' e a''' DG_line
        ⟨ha'_off_DG, he_off_DG, ha'''_off_DG⟩
      -- Eliminate first two: ¬a'.sameSide e (case B-¬α) AND ¬a'.sameSide a''' (pasch_3)
      have he_ss_a'''_DG : e.sameSide a''' DG_line := by
        rcases hpig_DG with h1 | h2 | h3
        · exact absurd h1 ha'_ss_e_DG
        · exact absurd h2 hnot_a'_ss_a'''_DG
        · exact h3
      have ha'''_ss_e_DG : a'''.sameSide e DG_line := same_side_symm e a''' DG_line he_ss_a'''_DG
      -- sum_angles_onlyif a a''' a'' e FA DG_line → ∠a''':a:a'' = ∠a''':a:e + ∠e:a:a''
      have hsum := sum_angles_onlyif a a''' a'' e FA DG_line
        ⟨hFAon, hDGg, ha'''_FA, ha''_DG, ha'''_ne_a, ha''_ne_a, he_off_FA, he_off_DG,
         hFA_ne_DG, ha'''_ss_e_DG, ha''_ss_e_FA⟩
      -- ∠a''':a:a'' = ∟ and ∠e:a:a'' = ∟ → ∠a''':a:e = 0 → e on FA
      have hzero : ∠ a''':a:e = 0 := by linarith
      exact e_on_FA_absurd
        (degenerated_angle_onlyif a a''' e FA ⟨ha'''_ne_a, right_6, hFAon, ha'''_FA, hzero⟩).1

end Elements.Book3
