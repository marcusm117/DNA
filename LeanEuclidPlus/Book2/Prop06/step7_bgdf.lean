import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.7 sub: BG ∥ DF. BG ∥ CE and CE ∥ DF, so BG ∥ DF [Prop.~1.30]. Distinctness derived in-body:
   BG ≠ CE (b ∈ BG, ¬b ∈ CE), CE ≠ DF (c ∈ CE, ¬c ∈ DF), BG ≠ DF (b ∈ BG, ¬b ∈ DF). -/
theorem helper_2_6_step7_bgdf (b c : Point) (BG CE DF : Line)
    (hbBG : b.onLine BG) (hcCE : c.onLine CE)
    (hboffCE : ¬(b.onLine CE)) (hcoffDF : ¬(c.onLine DF)) (hboffDF : ¬(b.onLine DF))
    (hBGCE : ¬(BG.intersectsLine CE)) (hCEDF : ¬(CE.intersectsLine DF)) :
    ¬(BG.intersectsLine DF) := by
  euclid_intros
  have hBGneCE : BG ≠ CE := fun heq => hboffCE (heq ▸ hbBG)
  have hCEneDF : CE ≠ DF := fun heq => hcoffDF (heq ▸ hcCE)
  have hBGneDF : BG ≠ DF := fun heq => hboffDF (heq ▸ hbBG)
  euclid_apply (proposition_30 BG DF CE)
  euclid_finish

end Elements.Book2
