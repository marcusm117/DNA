import SystemE
import Book2.Prop99.step1
import Book2.Prop99.step2
import Book2.Prop99.step3
import Book2.Prop99.step4
import Book2.Prop99.step5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

-- SYNTHETIC FIXTURE — exercises the @assumption / euclid_assumption feature end-to-end:
--   • step2 — euclid_assumption with `use_override` (conjunct projection step1.1)
--   • step5 — an `@args` object-remap (x y z → a c e) on a typed hypothesis slot, and a
--             non-length `show` (angle equality), the two cases Prop99 originally failed to cover.
-- NOT added to Book2.lean; `git rm -r Book2/Prop99` to retire.

namespace Elements.Book2

theorem proposition_99 : ∀ (a c e : Point),
    (|(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|) ∧ (∠ a:c:e = ∠ a:c:e) :=
by
  euclid_intros
  euclid_sentence "2.99.1"
    "Let AC and CE be segments, noting that each equals itself."
    (step1 : |(a─c)| = |(a─c)| ∧ |(c─e)| = |(c─e)|) := by euclid_apply (helper_2_99_step1 a c e)
  -- @assumption ("AC equals AC", |(a─c)| = |(a─c)|, use_override step1.1)
  euclid_sentence "2.99.2"
    "Since AC equals AC, the sum of AC and CE equals AC plus CE."
    (step2 : |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|) := by euclid_apply (helper_2_99_step2 a c e (by euclid_assumption "AC equals AC" (show |(a─c)| = |(a─c)|; exact step1.1)))
  euclid_sentence "2.99.3"
    "Therefore AC plus CE equals AC plus CE."
    (step3 : |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|) := by euclid_apply (helper_2_99_step3 a c e (by euclid_assumption "" (show |(a─c)| + |(c─e)| = |(a─c)| + |(c─e)|; assumption)))
  euclid_sentence "2.99.4"
    "The angle ACE equals itself."
    (step4 : ∠ a:c:e = ∠ a:c:e) := by euclid_apply (helper_2_99_step4 a c e)
  -- @args: a c e
  euclid_sentence "2.99.5"
    "Since the angle ACE equals the angle ACE, the angle ACE equals itself once more."
    (step5 : ∠ a:c:e = ∠ a:c:e) := by euclid_apply (helper_2_99_step5 a c e (by euclid_assumption "" (show ∠ a:c:e = ∠ a:c:e; assumption)))
  exact ⟨step3, step5⟩

end Elements.Book2
