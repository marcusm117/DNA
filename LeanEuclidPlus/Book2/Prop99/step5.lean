import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- Binder names x y z (NOT a c e) on purpose: the Main call site remaps them via `-- @args: a c e`,
-- so the wired hypothesis slot must read `(by show ∠ a:c:e = ∠ a:c:e; assumption)` — the type in
-- the CALL SITE's names, not the helper's. (Exercises resolve_call_args' binder→arg substitution.)
theorem helper_2_99_step5 (x y z : Point)
  (h : ∠ x:y:z = ∠ x:y:z)
  : ∠ x:y:z = ∠ x:y:z :=
  h

end Elements.Book2
