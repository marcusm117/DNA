import SystemE
import Book1.Prop07.Main
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Contradiction: n is a third point on circle equidistant from d as k.
-- Case 1: n on AG → must be g or a (only circle pts on AG), both give |dn| ≠ |dk|.
-- Case 2: n off AG → same_side_pigeon_hole → prop_7 (I.7) in each sub-case.
theorem helper_3_8_step31
    (ABC : Circle) (m k d b0 n g a : Point) (AG MK : Line)
    (hm : m.isCentre ABC)
    (hk : k.onCircle ABC) (hb0_circ : b0.onCircle ABC)
    (hn_circ : n.onCircle ABC) (hg_circ : g.onCircle ABC) (ha_circ : a.onCircle ABC)
    (hdnotCircle : ¬d.onCircle ABC)
    (hn_dist : |(d─n)| = |(d─k)|)
    (hn_ne_k : n ≠ k) (hn_ne_b : n ≠ b0)
    (hkoffAG : ¬k.onLine AG) (hb0offAG : ¬b0.onLine AG)
    (hb0_opp_k : ¬b0.sameSide k AG)
    (hstep29 : |(d─b0)| = |(d─n)|)
    (hmAG : m.onLine AG) (hdAG : d.onLine AG)
    (hgAG : g.onLine AG) (haAG : a.onLine AG)
    (hbet_dgm : between d g m) (hbet_gma : between g m a)
    (hstep13_assumption2 : |(m─g)| = |(m─k)|)
    (hstep14 : |(d─g)| < |(d─k)|)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK) (hne_mk : m ≠ k) :
    False := by
  have hm_inside : m.insideCircle ABC := center_inside_circle m ABC hm
  have hne_dm : d ≠ m := by euclid_finish
  have hne_kd : k ≠ d := fun h => hdnotCircle (h ▸ hk)
  have hne_b0d : b0 ≠ d := fun h => hdnotCircle (h ▸ hb0_circ)
  have hne_nd : n ≠ d := fun h => hdnotCircle (h ▸ hn_circ)
  have hne_nm : n ≠ m := fun h => absurd (h ▸ hn_circ) (inside_not_on_circle m ABC hm_inside)
  have hne_b0m : b0 ≠ m := fun h => absurd (h ▸ hb0_circ) (inside_not_on_circle m ABC hm_inside)
  -- Strict triangle ineq via proposition_20 (formTriangle m d k, conclusion = |dm|+|mk| > |dk|)
  obtain ⟨KD20, hkKD20, hdKD20⟩ := line_from_points k d hne_kd
  have hft_mdk : formTriangle m d k AG KD20 MK := by euclid_finish
  have hdk_lt_sum : |(d─k)| < |(d─m)| + |(m─k)| := by
    linarith [Elements.Book1.proposition_20 m d k AG KD20 MK hft_mdk]
  have hradius_kn : |(m─k)| = |(m─n)| :=
    (point_on_circle_onlyif m k n ABC ⟨hm, hk, hn_circ⟩).symm
  have hradius_b0n : |(m─b0)| = |(m─n)| :=
    (point_on_circle_onlyif m b0 n ABC ⟨hm, hb0_circ, hn_circ⟩).symm
  by_cases hnAG : n.onLine AG
  · by_cases hng : n = g
    · -- n = g → |dn| = |dg| < |dk| contradiction
      subst hng; linarith [segment_symmetric d n, hn_dist]
    · by_cases hna : n = a
      · -- n = a → |dn| = |da| > |dk| (k off AG → strict triangle ineq)
        have hdn_eq_da : |(d─n)| = |(d─a)| := by rw [hna]
        have hradius_ka : |(m─k)| = |(m─a)| :=
          (point_on_circle_onlyif m k a ABC ⟨hm, hk, ha_circ⟩).symm
        have hbet_dga : between d g a := between_trans_out d g m a ⟨hbet_dgm, hbet_gma⟩
        have hda_dist : |(d─g)| + |(g─a)| = |(d─a)| := between_if d g a hbet_dga
        have hga_dist : |(g─m)| + |(m─a)| = |(g─a)| := between_if g m a hbet_gma
        have hdm_dist : |(d─g)| + |(g─m)| = |(d─m)| := between_if d g m hbet_dgm
        linarith [segment_symmetric m g, hstep13_assumption2, hradius_ka, hn_dist, hdn_eq_da,
                  hdk_lt_sum]
      · -- n ≠ g and n ≠ a: two circle_line_intersections calls → between_not_trans
        have hbet_nmg : between n m g :=
          circle_line_intersections m n g AG ABC ⟨hmAG, hnAG, hgAG, hm_inside, hn_circ, hg_circ, hng⟩
        have hbet_nma : between n m a :=
          circle_line_intersections m n a AG ABC ⟨hmAG, hnAG, haAG, hm_inside, hn_circ, ha_circ, hna⟩
        exact between_not_trans n m g a ⟨hbet_nmg, hbet_nma⟩ hbet_gma
  · rcases same_side_pigeon_hole k b0 n AG ⟨hkoffAG, hb0offAG, hnAG⟩ with h | h | h
    · -- k sameSide b0: contradicts ¬b0.sameSide k AG
      exact hb0_opp_k (same_side_symm k b0 AG h)
    · -- k sameSide n: proposition_7 with (m, d, k, n)
      obtain ⟨KD, hkKD, hdKD⟩ := line_from_points k d hne_kd
      obtain ⟨MN, hmMN, hnMN⟩ := line_from_points m n hne_nm.symm
      obtain ⟨ND, hnND, hdND⟩ := line_from_points n d hne_nd
      exact Elements.Book1.proposition_7 m d k n AG MK KD MN ND
        ⟨⟨hmAG, hdAG, hne_dm.symm⟩, ⟨hMKm, hMKk, hne_mk⟩, ⟨hkKD, hdKD, hne_kd⟩,
         ⟨hmMN, hnMN, hne_nm.symm⟩, ⟨hnND, hdND, hne_nd⟩,
         h, hn_ne_k.symm, hradius_kn,
         by linarith [hn_dist, segment_symmetric k d, segment_symmetric n d]⟩
    · -- b0 sameSide n: proposition_7 with (m, d, b0, n)
      obtain ⟨MB0, hmMB0, hb0MB0⟩ := line_from_points m b0 hne_b0m.symm
      obtain ⟨B0D, hb0B0D, hdB0D⟩ := line_from_points b0 d hne_b0d
      obtain ⟨MN2, hmMN2, hnMN2⟩ := line_from_points m n hne_nm.symm
      obtain ⟨ND2, hnND2, hdND2⟩ := line_from_points n d hne_nd
      exact Elements.Book1.proposition_7 m d b0 n AG MB0 B0D MN2 ND2
        ⟨⟨hmAG, hdAG, hne_dm.symm⟩, ⟨hmMB0, hb0MB0, hne_b0m.symm⟩,
         ⟨hb0B0D, hdB0D, hne_b0d⟩,
         ⟨hmMN2, hnMN2, hne_nm.symm⟩, ⟨hnND2, hdND2, hne_nd⟩,
         h, hn_ne_b.symm, hradius_b0n,
         by linarith [hstep29, segment_symmetric b0 d, segment_symmetric n d]⟩

end Elements.Book3
