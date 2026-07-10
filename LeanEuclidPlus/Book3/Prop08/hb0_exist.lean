import SystemE
import Book1Variants.Prop23
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Construct b0 on circle ABC, on the opposite side of AG from k, with ∠d:m:b0 = ∠k:m:d.
-- Strategy:
--  1. proposition_23' places f with ∠f:m:d = ∠k:m:d on the opposite side of AG from k.
--  2. Extend line MF past m to get p; intersection_circle_line_extending_points gives b0
--     on circle on line MF between b0 and p (so b0 is on the SAME side as f from m).
--  3. equal_angles gives ∠b0:m:d = ∠f:m:d, same-side pigeon-hole places b0 opposite k.
theorem helper_3_8_hb0_exist
    (ABC : Circle) (m k l d g a : Point) (AG MK : Line)
    (hm : m.isCentre ABC)
    (hk : k.onCircle ABC)
    (hgAG : g.onLine AG) (haAG : a.onLine AG) (hdAG : d.onLine AG)
    (hbet_dgm : between d g m) (hbet_gma : between g m a)
    (hss_lk : l.sameSide k AG)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK) (hne_mk : m ≠ k) :
    ∃ b0 : Point, b0.onCircle ABC ∧ b0.opposingSides k AG ∧ ∠ d:m:b0 = ∠ k:m:d := by
  have hmAG : m.onLine AG := by euclid_finish
  have hkoffAG : ¬k.onLine AG := same_side_not_on_line k l AG (same_side_symm l k AG hss_lk)
  have hne_dm : d ≠ m := by euclid_finish
  -- Get x0 on opposite side of AG from k
  obtain ⟨x0, hx0_opp⟩ := exists_point_opposite AG k hkoffAG
  have hx0_offAG : ¬x0.onLine AG := hx0_opp.1
  -- formRectilinearAngle k m d for proposition_23'
  have hfra : formRectilinearAngle k m d MK AG := by euclid_finish
  -- f with ∠f:m:d = ∠k:m:d on opposite side of AG from k (same side as x0)
  -- a=m, b=d, c=m (vertex), d_param=k, e=d, x=x0: ∠f:m:d = ∠k:m:d
  obtain ⟨f, hfne, hfside_or_on, hfang⟩ :=
    Elements.Book1.proposition_23' m d m k d x0 AG MK AG ⟨by euclid_finish, hfra, hx0_offAG⟩
  -- f is off AG (angle ∠k:m:d > 0 since k off AG, so ∠f:m:d > 0, so f not collinear with m, d)
  have hfoffAG : ¬f.onLine AG := by euclid_finish
  -- f is on the same side as x0 (opposite from k)
  have hfside : f.sameSide x0 AG := hfside_or_on.resolve_left hfoffAG
  -- f.opposingSides k AG: f off AG, k off AG, ¬f.sameSide k AG
  have hfoppk : f.opposingSides k AG := by
    refine ⟨hfoffAG, hkoffAG, fun hfk => ?_⟩
    -- f.sameSide k ∧ f.sameSide x0 → k.sameSide x0 → x0.sameSide k → contradicts x0.opposingSides k
    exact hx0_opp.2.2 (same_side_symm k x0 AG (same_side_trans f k x0 AG ⟨hfk, hfside⟩))
  -- Line MF through m and f
  obtain ⟨MF, hmMF, hfMF⟩ := line_from_points m f hfne.symm
  -- Extend past m from f to get p (between f m p, p on opposite side of m from f)
  obtain ⟨p, hpMF, hbet_fmp⟩ := extend_point MF f m ⟨hfMF, hmMF, hfne⟩
  -- m is inside circle (it's the centre)
  have hmInside : m.insideCircle ABC := center_inside_circle m ABC hm
  -- m ≠ p from between f m p
  have hne_mp : m ≠ p := by euclid_finish
  -- Circle intersection on line MF: b0 between b0 m p (b0 on same side as f from m)
  obtain ⟨b0, hb0circ, hb0MF, hbet_b0mp⟩ :=
    intersection_circle_line_extending_points ABC MF m p ⟨hmInside, ⟨hmMF, hpMF, hne_mp⟩⟩
  -- b0 ≠ m (b0 on circle, m is centre = inside circle, not on it)
  have hmNotCircle : ¬m.onCircle ABC := by euclid_finish
  have hne_b0m : b0 ≠ m := fun h => hmNotCircle (h ▸ hb0circ)
  -- ¬between b0 m f: both b0 and f are on the same side of m (before m going to p)
  have hnotbet_b0mf : ¬between b0 m f := by euclid_finish
  -- b0 off AG (otherwise MF = AG contradicting f off AG)
  have hb0offAG : ¬b0.onLine AG := by euclid_finish
  -- p off AG (m is between f and p on MF; f off AG; so p off AG too)
  have hpoffAG : ¬p.onLine AG := by euclid_finish
  -- pasch_3: m between f and p on line, m on AG → f and p on opposite sides of AG
  have hfnotsamep : ¬f.sameSide p AG := pasch_3 f m p AG ⟨hbet_fmp, hmAG⟩
  have hb0notsamep : ¬b0.sameSide p AG := pasch_3 b0 m p AG ⟨hbet_b0mp, hmAG⟩
  -- pigeon-hole: f, b0, p all off AG; ¬f.sameSide p and ¬b0.sameSide p → f.sameSide b0
  have hfb0same : f.sameSide b0 AG := by
    rcases same_side_pigeon_hole f b0 p AG ⟨hfoffAG, hb0offAG, hpoffAG⟩ with h | h | h
    · exact h
    · exact absurd h hfnotsamep
    · exact absurd h hb0notsamep
  -- ∠b0:m:d = ∠f:m:d by equal_angles (both b0, f on same ray from m on line MF)
  have hangle_eq : ∠ b0:m:d = ∠ f:m:d :=
    equal_angles m b0 f d d MF AG
      ⟨hmMF, hb0MF, hfMF, hmAG, hdAG, hdAG,
       hne_b0m, hfne, hne_dm, hne_dm, hnotbet_b0mf, by euclid_finish⟩
  -- ∠d:m:b0 = ∠b0:m:d = ∠f:m:d = ∠k:m:d
  have hsym : ∠ b0:m:d = ∠ d:m:b0 := angle_symm b0 m d ⟨hne_b0m, hne_dm.symm⟩
  have hgoal_ang : ∠ d:m:b0 = ∠ k:m:d := by linarith [hangle_eq, hfang, hsym]
  -- b0.opposingSides k AG: b0 off AG, k off AG, ¬b0.sameSide k AG
  have hb0fAG : b0.sameSide f AG := same_side_symm f b0 AG hfb0same
  have hb0_opp : b0.opposingSides k AG :=
    ⟨hb0offAG, hkoffAG, fun hb0k =>
      absurd (same_side_trans b0 f k AG ⟨hb0fAG, hb0k⟩) hfoppk.2.2⟩
  exact ⟨b0, hb0circ, hb0_opp, hgoal_ang⟩

end Elements.Book3
