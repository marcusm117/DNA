import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.13 sub: formTriangle d h b DG BE AB. d,h on DG; h,b on BE; b,d on AB. The three lines are
   pairwise distinct: DG ≠ BE (b ∉ DG, b ∈ BE), BE ≠ AB (h ∉ AB, h ∈ BE), AB ≠ DG (h ∉ AB, h ∈ DG).
   between b h e supplies h ≠ b; d ≠ h, d ≠ b from the off-line anchors. -/
theorem helper_2_5_step13_dhdb_tri (b d e h : Point) (AB BE DG : Line)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hbBE : b.onLine BE) (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hboffDG : ¬(b.onLine DG)) (hhoffAB : ¬(h.onLine AB))
    (hbhe : between b h e) :
    formTriangle d h b DG BE AB := by
  euclid_intros
  have hbh : b ≠ h := (between_symm b h e hbhe).2.1
  have hdh : d ≠ h := fun heq => hhoffAB (heq ▸ hdAB)
  have hdb : d ≠ b := fun heq => hboffDG (heq ▸ hdDG)
  have hDGBE : DG ≠ BE := fun heq => hboffDG (heq ▸ hbBE)
  have hBEAB : BE ≠ AB := fun heq => hhoffAB (heq ▸ hhBE)
  have hABDG : AB ≠ DG := fun heq => hhoffAB (heq ▸ hhDG)
  unfold formTriangle
  repeat' apply And.intro
  all_goals first | assumption

end Elements.Book2
