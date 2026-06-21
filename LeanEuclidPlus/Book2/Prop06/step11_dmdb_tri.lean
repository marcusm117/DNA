import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.11 sub: formTriangle b d h AB DE BG. b,d on AB; d,h on DE; b,h on BG. Pairwise distinct:
   AB ≠ DE (b ∉ DE, b ∈ AB), DE ≠ BG (b ∉ DE, b ∈ BG), AB ≠ BG (h ∉ AB, h ∈ BG). d ≠ h, b ≠ h from the
   off-line anchors; b ≠ d from between a b d. -/
theorem helper_2_6_step11_dmdb_tri (b d h : Point) (AB DE BG : Line)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hdDE : d.onLine DE) (hhDE : h.onLine DE)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hboffDE : ¬(b.onLine DE)) (hhoffAB : ¬(h.onLine AB)) (hbd : b ≠ d) :
    formTriangle b d h AB DE BG := by
  euclid_intros
  have hdh : d ≠ h := fun heq => hhoffAB (heq ▸ hdAB)
  have hbh : b ≠ h := fun heq => hhoffAB (heq ▸ hbAB)
  have hABDE : AB ≠ DE := fun heq => hboffDE (heq ▸ hbAB)
  have hDEBG : DE ≠ BG := fun heq => hboffDE (heq ▸ hbBG)
  have hABBG : AB ≠ BG := fun heq => hhoffAB (heq ▸ hhBG)
  unfold formTriangle
  repeat' apply And.intro
  all_goals first | assumption | euclid_finish

end Elements.Book2
