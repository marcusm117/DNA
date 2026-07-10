import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.9 sub: AK ∥ DF. AK ∥ CE and CE ∥ DF, so AK ∥ DF [Prop.~1.30]. Distinctness from off-line
   anchors: AK ≠ CE (a ∈ AK, ¬a ∈ CE), CE ≠ DF (c ∈ CE, ¬c ∈ DF), AK ≠ DF (a ∈ AK, ¬a ∈ DF). -/
theorem helper_2_6_step9_akdf (a c : Point) (AK CE DF : Line)
    (haAK : a.onLine AK) (hcCE : c.onLine CE)
    (haoffCE : ¬(a.onLine CE)) (hcoffDF : ¬(c.onLine DF)) (haoffDF : ¬(a.onLine DF))
    (hAKCE : ¬(AK.intersectsLine CE)) (hCEDF : ¬(CE.intersectsLine DF)) :
    ¬(AK.intersectsLine DF) := by
  euclid_intros
  have hAKneCE : AK ≠ CE := fun heq => haoffCE (heq ▸ haAK)
  have hCEneDF : CE ≠ DF := fun heq => hcoffDF (heq ▸ hcCE)
  have hAKneDF : AK ≠ DF := fun heq => haoffDF (heq ▸ haAK)
  euclid_apply (proposition_30 AK DF CE)
  euclid_finish

end Elements.Book2
