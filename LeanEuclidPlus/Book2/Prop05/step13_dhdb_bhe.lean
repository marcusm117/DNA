import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.13 sub: between b h e — h (= DG ∩ BE) lies between b and e on the diagonal BE. Given b,e on
   opposite sides of DG (hbopp) and h on both DG and BE, pasch_4 places h between them. Mirror of
   step6_bmf_bhe. -/
theorem helper_2_5_step13_dhdb_bhe (b e h : Point) (BE DG : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hhDG : h.onLine DG) (heoffDG : ¬(e.onLine DG)) (hboffDG : ¬(b.onLine DG))
    (hbe : b ≠ e) (hbopp : ¬(b.sameSide e DG)) :
    between b h e := by
  euclid_intros
  have hDGBE : DG ≠ BE := fun heq => heoffDG (heq ▸ heBE)
  have heh : e ≠ h := fun heq => heoffDG (heq ▸ hhDG)
  have hbh : b ≠ h := fun heq => hboffDG (heq ▸ hhDG)
  euclid_apply (pasch_4 b h e DG BE)
  euclid_finish

end Elements.Book2
