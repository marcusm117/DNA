import SystemE
import Helpers.SameSide
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21
    (a b c d : Point)
    (f g k h m l : Point)
    (FG KH FK GH LM : Line)
    (hk_KH : k.onLine KH)
    (hh_KH : h.onLine KH)
    (hg_GH : g.onLine GH)
    (hh_GH : h.onLine GH)
    (hg_FG : g.onLine FG)
    (hm_LM : m.onLine LM)
    (hl_LM : l.onLine LM)
    (hfk_GH : f.sameSide k GH)
    (hh_sg_LM : h.sameSide g LM)
    (step9 : k.opposingSides m GH ∧ ∠k:h:g + ∠g:h:m = ∟ + ∟)
    (step17_assumption2 : |(h─g)| = |(m─l)| ∧ ¬GH.intersectsLine LM)
    (step18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (step20 : formParallelogram f l k m FG KH FK LM)
    (step21_assumption1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
    (step21_assumption2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
    : Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  -- between k h m: h is on both GH and KH; k,m are opposite sides of GH
  have hf_not_GH : ¬f.onLine GH := same_side_not_on_line f k GH hfk_GH
  have hGH_ne_KH : GH ≠ KH := fun heq => step9.1.1 (heq ▸ hk_KH)
  have hkh : k ≠ h := fun heq => step9.1.1 (heq ▸ hh_GH)
  have hmh : m ≠ h := fun heq => step9.1.2.1 (heq ▸ hh_GH)
  have between_k_h_m : between k h m :=
    pasch_4 k h m GH KH ⟨hGH_ne_KH, hh_GH, hh_KH, step18.1, hkh, hmh, step9.1.2.2⟩
  -- between f g l: g is on both GH and FG; derive ¬f.sameSide l GH
  have hGH_ne_FG : GH ≠ FG := fun heq => hf_not_GH (heq ▸ step18.2.1)
  have hfg : f ≠ g := fun heq => hf_not_GH (heq ▸ hg_GH)
  have hg_not_LM : ¬g.onLine LM := same_side_not_on_line g h LM (same_side_symm h g LM hh_sg_LM)
  have hGH_ne_LM : GH ≠ LM := fun heq => hg_not_LM (heq ▸ hg_GH)
  have hl_not_GH : ¬l.onLine GH := fun hl_GH =>
    step17_assumption2.2 (intersection_lines_common_point l GH LM ⟨hl_GH, hl_LM, hGH_ne_LM⟩)
  have hlg : l ≠ g := fun heq => hl_not_GH (heq ▸ hg_GH)
  have hlm_ss_GH : l.sameSide m GH :=
    sameSide_of_parallel' l m l LM GH hl_LM hm_LM hl_LM hl_not_GH
      (fun h => step17_assumption2.2 (intersection_symm LM GH h))
  have hf_not_ss_m : ¬f.sameSide m GH := fun hssm =>
    step9.1.2.2 (same_side_trans f k m GH ⟨hfk_GH, hssm⟩)
  have hf_not_ss_l : ¬f.sameSide l GH := fun hssl =>
    hf_not_ss_m (same_side_trans l f m GH ⟨same_side_symm f l GH hssl, hlm_ss_GH⟩)
  have between_f_g_l : between f g l :=
    pasch_4 f g l GH FG ⟨hGH_ne_FG, hg_GH, hg_FG, step18.2, hfg, hlg, hf_not_ss_l⟩
  -- sum_parallelograms_area decomposes (△f:k:m) + (△f:m:l) into 4 sub-triangles
  have h_sum := sum_parallelograms_area f l k m g h FG KH FK LM
    ⟨step20, between_f_g_l, between_k_h_m⟩
  -- area_symm_2 reorients (△g:m:l) → (△g:l:m) and (△f:m:l) → (△f:l:m)
  linarith [h_sum, area_symm_2 g m l, area_symm_2 f m l, step21_assumption1, step21_assumption2]

end Elements.Book1
