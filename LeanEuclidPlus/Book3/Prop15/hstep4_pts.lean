import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_hstep4_pts
    (e k l h f m0 : Point) (ABCD : Circle) (FG EK MN : Line)
    (h_centre : e.isCentre ABCD)
    (h_f_circ : f.onCircle ABCD)
    (hEK : distinctPointsOnLine e k EK)
    (h_k_fg : k.onLine FG)
    (h_f_fg : f.onLine FG)
    (h_angle_ekf : ∠ e:k:f = ∟)
    (h_el_eq : |(e─l)| = |(e─h)|)
    (h_eh_lt_ek : |(e─h)| < |(e─k)|)
    (hl_betw : between e l k)
    (hm0_off : ¬m0.onLine EK)
    (hm0_perp : ∠ e:l:m0 = ∟)
    (hMN : distinctPointsOnLine l m0 MN) :
    ∃ m n : Point, m.onCircle ABCD ∧ n.onCircle ABCD ∧ between m l n ∧ ∠ m:l:e = ∟ ∧
    m.onLine MN ∧ n.onLine MN := by
  -- Sub-node: l inside ABCD (backed by hstep4_pts_lin.lean)
  have hstep4_pts_lin : l.insideCircle ABCD := by sorry
  -- Derived facts (stable; hEK/hMN not consumed by obtain)
  have h_l_on_MN : l.onLine MN := hMN.1
  have h_m0_on_MN : m0.onLine MN := hMN.2.1
  have h_l_on_EK : l.onLine EK := between_same_line_in e l k EK ⟨hl_betw, hEK.1, hEK.2.1⟩
  have h_e_ne_l : e ≠ l := (between_symm e l k hl_betw).2.1
  have h_m0_ne_l : m0 ≠ l := Ne.symm hMN.2.2
  -- MN intersects ABCD (l inside + l on MN)
  have h_int : MN.intersectsCircle ABCD :=
    intersection_circle_line_2 l ABCD MN ⟨hstep4_pts_lin, h_l_on_MN⟩
  -- Get m, n on circle and on MN via obtain (euclid_apply as m n only introduces m)
  obtain ⟨m, h_rest_m⟩ := intersections_circle_line ABCD MN h_int
  obtain ⟨n, hm_on, hm_MN, hn_on, hn_MN, hmn_ne⟩ := h_rest_m
  -- between m l n (l inside, m and n on circle, all on MN)
  have h_bet : between m l n :=
    circle_line_intersections l m n MN ABCD ⟨h_l_on_MN, hm_MN, hn_MN,
      hstep4_pts_lin, hm_on, hn_on, hmn_ne⟩
  -- m ≠ l and n ≠ l (inside/outside)
  have h_m_ne_l : m ≠ l := (between_symm m l n h_bet).2.1
  -- ¬(e.onLine MN): if e on MN, then EK = MN, so m0.onLine EK — contradicts hm0_off
  have h_e_off_MN : ¬e.onLine MN := fun h_e_on =>
    absurd h_m0_on_MN ((two_points_determine_line e l EK MN
      ⟨⟨hEK.1, h_l_on_EK, h_e_ne_l⟩, h_e_on, h_l_on_MN⟩) ▸ hm0_off)
  -- ¬(m.onLine EK): if m on EK, then EK = MN, so m0.onLine EK — contradicts hm0_off
  have h_m_off_EK : ¬m.onLine EK := fun h_m_on =>
    absurd h_m0_on_MN ((two_points_determine_line l m EK MN
      ⟨⟨h_l_on_EK, h_m_on, h_m_ne_l.symm⟩, h_l_on_MN, hm_MN⟩) ▸ hm0_off)
  -- perpendicular_onlyif: ∠ e:l:m0 = ∠ m0:l:k (from right angle at l on EK)
  have h_perp_m0 : ∠ e:l:m0 = ∠ m0:l:k :=
    perpendicular_onlyif e k l m0 EK ⟨hEK.1, hEK.2.1, hl_betw, hm0_off, hm0_perp⟩
  -- ∠ m:l:e = ∟ by case split on whether m is on same side of l as m0 on MN
  have h_angle : ∠ m:l:e = ∟ := by
    by_cases h_side : ¬(between m l m0)
    · -- Same side: equal_angles gives ∠ e:l:m = ∠ e:l:m0 = ∟
      have h_eq : ∠ e:l:m = ∠ e:l:m0 :=
        equal_angles l e e m m0 EK MN ⟨h_l_on_EK, hEK.1, hEK.1, h_l_on_MN,
          hm_MN, h_m0_on_MN,
          h_e_ne_l, h_e_ne_l, h_m_ne_l, h_m0_ne_l,
          fun h_bad => (between_symm e l e h_bad).2.2.1 rfl,
          h_side⟩
      exact (angle_symm m l e ⟨h_m_ne_l, Ne.symm h_e_ne_l⟩).trans (h_eq.trans hm0_perp)
    · -- Opposite side: between m l m0; n is on same side as m0 (by between_not_trans)
      push_neg at h_side
      have h_n_ne_l : n ≠ l := by euclid_finish
      have h_n_same : ¬(between n l m0) := between_not_trans m l n m0 ⟨h_bet, h_side⟩
      have h_eq_n : ∠ e:l:n = ∠ e:l:m0 :=
        equal_angles l e e n m0 EK MN ⟨h_l_on_EK, hEK.1, hEK.1, h_l_on_MN,
          hn_MN, h_m0_on_MN,
          h_e_ne_l, h_e_ne_l, h_n_ne_l, h_m0_ne_l,
          fun h_bad => (between_symm e l e h_bad).2.2.1 rfl,
          h_n_same⟩
      have h_eln : ∠ e:l:n = ∟ := h_eq_n.trans hm0_perp
      have h_nle : ∠ n:l:e = ∟ :=
        (angle_symm n l e ⟨h_n_ne_l, Ne.symm h_e_ne_l⟩).trans h_eln
      -- perpendicular_onlyif (reversed): ∠ n:l:e = ∟ on MN → ∠ n:l:e = ∠ e:l:m
      have h_nm : ∠ n:l:e = ∠ e:l:m :=
        perpendicular_onlyif n m l e MN ⟨hn_MN, hm_MN,
          (between_symm m l n h_bet).1, h_e_off_MN, h_nle⟩
      exact (angle_symm m l e ⟨h_m_ne_l, Ne.symm h_e_ne_l⟩).trans
            (h_nm.symm.trans h_nle)
  exact ⟨m, n, hm_on, hn_on, h_bet, h_angle, hm_MN, hn_MN⟩

end Elements.Book3
