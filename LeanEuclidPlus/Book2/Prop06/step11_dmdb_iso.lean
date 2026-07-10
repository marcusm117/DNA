import SystemE
import Book1Variants.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.11 sub: ∠ c:d:e = ∠ c:e:d. Triangle CDE is isosceles — |c─d| = |c─e| (the square's two sides
   from C) — with AB (c,d), DE (d,e), CE (c,e) forming it and ∠ d:c:e = ∟ pinning non-collinearity,
   so its base angles at D and E are equal [Prop.~1.5]. -/
theorem helper_2_6_step11_dmdb_iso (c d e : Point) (AB DE CE : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hce_cd : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) (hcoffDE : ¬(c.onLine DE)) :
    ∠ c:d:e = ∠ c:e:d := by
  euclid_intros
  have hABDE : AB ≠ DE := fun heq => hcoffDE (heq ▸ hcAB)
  have hCEDE : CE ≠ DE := fun heq => hcoffDE (heq ▸ hcCE)
  have hABCE : AB ≠ CE := by
    intro heq; euclid_finish
  have htri : formTriangle c d e AB DE CE := by
    unfold formTriangle
    repeat' apply And.intro
    all_goals first | assumption | euclid_finish
  euclid_apply (proposition_5' c d e AB DE CE)
  euclid_finish

end Elements.Book2
