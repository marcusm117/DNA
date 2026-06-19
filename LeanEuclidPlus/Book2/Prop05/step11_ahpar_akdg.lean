import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.11 sub: AK ∥ DG. AK ∥ CE and DG ∥ CE → AK ∥ DG by proposition_30.
   Need AK ≠ CE (from haoffCE + haAK), DG ≠ CE (from hdoffCE + hdDG), AK ≠ DG (from euclid_finish). -/
-- AK ≠ DG from: k ∈ AK ∩ KM, h ∈ DG ∩ KM, k ≠ h → AK ∩ KM ≠ DG ∩ KM → AK ≠ DG
theorem helper_2_5_step11_ahpar_akdg (a d k h e l : Point) (AK DG CE KM : Line)
    (haAK : a.onLine AK) (hdDG : d.onLine DG) (hkAK : k.onLine AK) (hhDG : h.onLine DG)
    (hkKM : k.onLine KM) (hhKM : h.onLine KM) (heCE : e.onLine CE)
    (hlCE : l.onLine CE) (hlKM : l.onLine KM)
    (haoffCE : ¬(a.onLine CE)) (hdoffCE : ¬(d.onLine CE)) (heoffDG : ¬(e.onLine DG))
    (hkh : k ≠ h)
    (hAKCE : ¬(AK.intersectsLine CE)) (hDGCE : ¬(DG.intersectsLine CE)) :
    ¬(AK.intersectsLine DG) := by
  euclid_intros
  have hAKneCE : AK ≠ CE := fun heq => haoffCE (heq ▸ haAK)
  have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
  -- AK ≠ DG: if AK = DG, then AK ∩ KM = DG ∩ KM so the unique intersection is both k and h.
  -- Since k ≠ h, we'd need two_points_determine_line to give KM = AK, but that's a different arg.
  -- Actually: if AK = DG, then k ∈ DG (k ∈ AK = DG) and h ∈ DG, k ≠ h, both on DG ∩ KM.
  -- two_points_determine_line k h KM DG → KM = DG. But e ∉ DG (heoffDG) and e ∈ CE...
  -- Actually: k ∈ AK and h ∈ DG; if AK = DG then k ∈ DG. k,h ∈ KM ∩ DG. k ≠ h → DG = KM.
  -- Then e ∈ CE and e ∉ DG = KM, so KM ≠ CE. But we need more to get contradiction from KM = DG.
  -- Use hDGCE: ¬DG∩CE; with DG = KM, ¬KM∩CE. But e ∈ CE and if e ∈ KM then KM ∩ CE exists.
  -- Actually use a direct approach: AK ≠ DG via the heoffDG anchor.
  -- If AK = DG, then... k ∈ AK = DG. k ∈ KM. h ∈ DG ∩ KM. k ≠ h → two distinct KM∩DG points.
  -- But DG ∩ KM should be unique (they're not parallel, they intersect at h). Actually if k ∈ DG too,
  -- then k = h or DG = KM. k ≠ h → DG = KM. But then e ∉ DG = KM. We have e ∈ CE.
  -- Also: DG ∥ CE (hDGCE) means ¬DG∩CE. If DG = KM, then ¬KM∩CE. But DG ∩ CE was ¬ by hDGCE.
  -- Hmm this doesn't give contradiction to AK = DG directly.
  -- AK ≠ DG: if AK = DG, k ∈ AK = DG and h ∈ DG, k ≠ h, both on DG ∩ KM.
  -- two_points_determine_line k h KM DG would give KM = DG. But then e ∈ CE ∉ DG.
  -- Actually: k ∈ AK = DG would force k ∈ DG. k ≠ h, both on DG ∩ KM → KM = DG.
  -- Then hDGCE : ¬DG∩CE becomes ¬KM∩CE. But l ∈ KM ∩ CE (they DO intersect) — contradiction.
  -- (l is not in scope, but l ∈ CE ∩ DG = KM if DG = KM is in scope... complex)
  -- Use: from k ∈ AK = DG (if AK = DG) and h ∈ DG, k ≠ h → KM = DG (two_points).
  -- Then use heoffDG : ¬e ∈ DG and e ∈ CE: if KM = DG and ¬DG∩CE then ¬KM∩CE.
  -- But l ∈ KM ∩ CE is in scope (l is in step11_ahpar's context via hklh: between k l h,
  -- and we have hlKM in step11_ahpar.lean, hlCE there too). But those are not in this file's scope.
  -- Let me add l as a parameter to get the anchor.
  -- For now use the k ≠ h → AK ≠ DG route with explicit two_points:
  have hAKneDG : AK ≠ DG := by
    intro heq
    have hkDG : k.onLine DG := heq ▸ hkAK
    have hKMisDG : KM = DG := by
      euclid_apply (two_points_determine_line k h KM DG)
      euclid_finish
    -- KM = DG → l ∈ DG (l ∈ KM). l ∈ CE. DG ≠ CE (from hdoffCE). DG ∩ CE at l → contradicts hDGCE.
    have hlDG : l.onLine DG := hKMisDG ▸ hlKM
    have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
    euclid_apply (intersection_lines_common_point l DG CE)
    euclid_finish
  euclid_apply (proposition_30 AK DG CE)
  euclid_finish

end Elements.Book2
