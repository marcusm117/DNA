import SystemE
import Book2.Prop99.step1
import Book2.Prop99.step2
import Book2.Prop99.step3
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

-- SYNTHETIC FIXTURE — exercises the @assumption / euclid_assumption feature end-to-end.
-- NOT added to Book2.lean; `git rm -r Book2/Prop99` to retire.

namespace Elements.Book2

theorem proposition_99 : ∀ (a c e : Point),
    |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)| :=
by
  euclid_intros
  euclid_sentence "2.99.1"
    "Let AC and CE be segments, noting that each equals itself."
    (step1 : |(a─c)| = |(a─c)| ∧ |(c─e)| = |(c─e)|) := by euclid_apply (helper_2_99_step1 a c e)
  -- @assumption ("AC equals AC", |(a─c)| = |(a─c)|, use_override step1.1)
  euclid_sentence "2.99.2"
    "Since AC equals AC, the sum of AC and CE equals AC plus CE."
    (step2 : |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|) := by euclid_apply (helper_2_99_step2 a c e (by euclid_assumption "AC equals AC" |(a─c)| = |(a─c)| use_override step1.1))
  euclid_sentence "2.99.3"
    "Therefore AC plus CE equals AC plus CE."
    (step3 : |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|) := by euclid_apply (helper_2_99_step3 a c e (by show |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|; assumption))
  exact step3

end Elements.Book2
