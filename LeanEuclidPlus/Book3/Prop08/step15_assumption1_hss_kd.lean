import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Goal: d.sameSide k ML
-- Strategy: triple_incidence_2 with a=m, L=AG, M=MK, N=ML, b=d, c=k, δ=l
--   Needs: k.sameSide l AG (hss_lk symm), ¬(d.sameSide l MK), ¬(l.onLine MK), d≠m
-- For ¬(d.sameSide l MK):
--   same_side_pigeon_hole on {g,l,a} off MK + pasch facts
--   Case g.sameSide l MK:
--     → d.sameSide l MK (via same_side_trans through g)
--     → sum_angles_onlyif(m,k,d,l,MK,AG) gives ∠k:m:d = ∠k:m:l + ∠l:m:d
--     → linarith with ∠k:m:d < ∠l:m:d and 0 ≤ ∠k:m:l → contradiction
--   Case g.sameSide a MK: contradiction with ¬g.sameSide a MK
--   Case l.sameSide a MK: → ¬(d.sameSide l MK) by transitivity with ¬d.sameSide a MK
theorem helper_3_8_step15_assumption1_hss_kd (m k l d g a h : Point)
    (MK ML AG : Line)
    (hdAG : d.onLine AG) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hbetdgm : between d g m) (hbetgma : between g m a)
    (hangle_kl : ∠k:m:d < ∠l:m:d)
    (hangle_lh : ∠l:m:d < ∠h:m:d)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK)
    (hMLm : m.onLine ML) (hMLl : l.onLine ML)
    (hmAG : m.onLine AG)
    (hne_lm : l ≠ m) (hne_km : k ≠ m) (hne_dm : m ≠ d)
    (hloffAG : ¬l.onLine AG) (hkoffAG : ¬k.onLine AG)
    (hss_lk : l.sameSide k AG) :
    d.sameSide k ML := by
  -- Line distinctness
  have hne_ml : ML ≠ AG := fun h => hloffAG (h ▸ hMLl)
  have hne_mk_ag : MK ≠ AG := fun h => hkoffAG (h ▸ hMKk)
  -- Betweenness chain: between d g m + between g m a → between d m a
  have hbet_mgd : between m g d := (between_symm d g m hbetdgm).1
  have hbet_amg : between a m g := (between_symm g m a hbetgma).1
  have hne_gm : g ≠ m := by euclid_finish
  have hne_am : a ≠ m := (between_symm a m g hbet_amg).2.1
  have hbet_amd : between a m d := between_trans_out a m g d ⟨hbet_amg, hbet_mgd⟩
  have hbet_dma : between d m a := (between_symm a m d hbet_amd).1
  -- Off-line facts for ML
  have hdoffML : ¬d.onLine ML := fun h => hne_ml (by euclid_finish)
  have haoffML : ¬a.onLine ML := fun h => hne_ml (by euclid_finish)
  have hgoffML : ¬g.onLine ML := fun h => hne_ml (by euclid_finish)
  have hkoffML : ¬k.onLine ML := by euclid_finish
  -- Off-line facts for MK
  have hgoffMK : ¬g.onLine MK := fun h => hne_mk_ag (by euclid_finish)
  have hdoffMK : ¬d.onLine MK := fun h => hne_mk_ag (by euclid_finish)
  have haoffMK : ¬a.onLine MK := fun h => hne_mk_ag (by euclid_finish)
  have hne_mk_ml : MK ≠ ML := fun h => hkoffML (h ▸ hMKk)
  have hloffMK : ¬l.onLine MK := fun h => hne_mk_ml (by euclid_finish)
  -- Pasch facts for MK
  have hss_gdMK : g.sameSide d MK := pasch_2 m g d MK ⟨hbet_mgd, hMKm, hgoffMK⟩
  have hnotss_daMK : ¬d.sameSide a MK := pasch_3 d m a MK ⟨hbet_dma, hMKm⟩
  have hnotss_gaMK : ¬g.sameSide a MK :=
    fun hga => hnotss_daMK (same_side_trans g d a MK ⟨hss_gdMK, hga⟩)
  -- l.sameSide a MK via pigeon hole on {g, l, a} off MK
  have hss_laMK : l.sameSide a MK := by
    rcases same_side_pigeon_hole g l a MK ⟨hgoffMK, hloffMK, haoffMK⟩ with h1 | h2 | h3
    · -- h1: g.sameSide l MK → d.sameSide l MK → angle contradiction
      exfalso
      have hdl_MK : d.sameSide l MK :=
        same_side_trans g d l MK ⟨hss_gdMK, h1⟩
      have hang_sum : (∠k:m:d : ℝ) = ∠k:m:l + ∠l:m:d :=
        sum_angles_onlyif m k d l MK AG ⟨hMKm, hmAG, hMKk, hdAG, Ne.symm hne_km, hne_dm,
          hloffMK, hloffAG, hne_mk_ag, same_side_symm l k AG hss_lk, hdl_MK⟩
      linarith [(angle_range (Angle.ofPoints k m l)).1]
    · exact absurd h2 hnotss_gaMK
    · exact h3
  -- ¬(d.sameSide l MK): l on a's side (hss_laMK), d on opposite side (hnotss_daMK)
  have hnotss_dlMK : ¬d.sameSide l MK :=
    fun hdl => hnotss_daMK (same_side_trans l d a MK ⟨same_side_symm d l MK hdl, hss_laMK⟩)
  -- triple_incidence_2: L=AG, M=MK, N=ML, a=m, b=d, c=k, δ=l → d.sameSide k ML
  exact triple_incidence_2 AG MK ML m d k l
    ⟨hmAG, hMKm, hMLm, hdAG, hMKk, hMLl,
      same_side_symm l k AG hss_lk, hnotss_dlMK, hloffMK, Ne.symm hne_dm⟩

end Elements.Book3
