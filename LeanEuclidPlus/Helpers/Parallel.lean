import SystemE
import Book.Prop30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements

open Elements.Book1

/- Shared "parallel transitivity" lemma — the formal-gap glue for chaining two non-intersections.
   `L1 ∦ L2` and `L2 ∦ L3` (with the three lines pairwise distinct) ⟹ `L1 ∦ L3`, via
   `proposition_30` (two lines each parallel to a third are parallel to each other).

   Hypotheses are ATOMIC (`¬(L.intersectsLine M)`, `L ≠ M`) so the pipeline discharges them
   positionally with `(by assumption)`. The three distinctness facts are the precondition
   `proposition_30` needs in context — the caller derives each as a cheap line-≠ term from an
   off-line anchor (`fun heq => hpoffM (heq ▸ hpL)`) before wiring this.
   (Generalizes e.g. Prop05 step7_dfpar_dgbf {L1,L2,L3 = DG,CE,BF} and Prop04 step9_cfbe
   {CF,AD,BE}, whose bodies are this exact chain.) -/
theorem not_intersects_trans (L1 L2 L3 : Line)
    (h12 : ¬(L1.intersectsLine L2)) (h23 : ¬(L2.intersectsLine L3))
    (hne12 : L1 ≠ L2) (hne23 : L2 ≠ L3) (hne13 : L1 ≠ L3) :
    ¬(L1.intersectsLine L3) := by
  euclid_apply (proposition_30 L1 L3 L2)
  euclid_finish

end Elements
