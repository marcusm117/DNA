import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub-sub: between b h e — h (= DG ∩ BE) lies between b and e on the diagonal BE. Given b,e on
   opposite sides of DG (hyp step6_bmf_bopp, a sibling sub-node) and h = DG ∩ BE on both lines,
   pasch_4 b h e DG BE places h between them. Slim signature so the pasch euclid_finish stays fast. -/
theorem helper_2_5_step6_bmf_bhe (b e h : Point) (BE DG : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hhDG : h.onLine DG) (heoffDG : ¬(e.onLine DG)) (hboffDG : ¬(b.onLine DG))
    (hbe : b ≠ e) (hbopp : ¬(b.sameSide e DG)) :
    between b h e := by
  euclid_intros
  -- all pasch_4 distinctness as cheap terms: DG≠BE (e∈BE, e∉DG); e≠h (e∉DG, h∈DG); b≠h (b∉DG, h∈DG).
  have hDGBE : DG ≠ BE := fun heq => heoffDG (heq ▸ heBE)
  have heh : e ≠ h := fun heq => heoffDG (heq ▸ hhDG)
  have hbh : b ≠ h := fun heq => hboffDG (heq ▸ hhDG)
  euclid_apply (pasch_4 b h e DG BE)
  euclid_finish

end Elements.Book2
