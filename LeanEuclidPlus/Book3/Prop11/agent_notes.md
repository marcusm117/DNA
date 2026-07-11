# Prop11 (III.11) — agent notes

## State (2026-07-10) — PHASE B COMPLETE (all 13 nodes --drive-green; --all witness running)
- Signature fix `|(g─a)| < |(f─a)|` (r_ADE < r_ABC) ADDED to proposition_11 and VERIFIED valid+required
  (see ROOT CAUSE below — counterexample re-checked independently). ⚠ NEEDS human `check_signatures.py
  --save` + `check_steps.py --save` at gate C (working-tree sig differs from proposition_signatures.json).
- step_nhout_hin now builds ZERO-sorry via the pf-construction (hradii threaded through step_nhout →
  step_nhout_hin; `hpf_in_ABC : pf.insideCircle ABC := by euclid_finish` closes with hradii present).
- step3 cites [Prop.~1.20]: cone now `euclid_apply (Elements.Book1.proposition_20 g a f AG AF FG)`
  (euclid_apply discharges formTriangle — euclid_finish derives ¬a.onLine FG from hradii). criterion-3 ✓.
- step8 (=habsurd1), step9 (¬¬-elim) proven; Main tail `exact step9`. Dead `hgap.lean` deleted.
- whole-prop checks: criterion-3 ✓ · integrity ✓ · no orphans ✓.

## (historical) earlier state
- step1..step7 ✓ certified. step8, step9 trivial-but-blocked (in-order) behind step_nhout.
- `step_nhout` = @euclid_gap: `by_cases h_out : h.outsideCircle ADE`.
  - MAIN branch (h outside ADE) = Euclid's actual argument, steps 2–7. Done.
  - else branch splits (trichotomy) into `step_nhout_hon` (h ON ADE) and `step_nhout_hin` (h INSIDE ADE),
    each must derive `False` → together they give `h.outsideCircle ADE` by elimination.
- **`step_nhout_hon` ✓ builds zero-sorry** (P ok). Route: build centre-line FG (through f=centre ABC),
  take the FAR intersection h' of FG with ABC via `intersection_circle_line_extending_points`
  (`between h' g h`), prove `h'.outsideCircle ADE` (euclid_finish, pinned by `|g-h|=|g-a|`), then
  `intersection_circle_circle_1 g h' ABC ADE` (g inside ADE & ABC; h' on ABC & outside ADE) contradicts ¬intersect.

## ROOT CAUSE FOUND: proposition_11 signature is FALSE as stated (Phase-A bug)
The current signature does NOT pin ADE as the inner circle — `g.insideCircle ABC` holds whether ADE is
inside ABC or ABC is inside ADE. **Counterexample satisfying every hypothesis:** ABC=(centre f, r=1),
ADE=(centre g, r=1.5), |fg|=0.5, internally tangent at a with ABC INSIDE ADE. All hyps hold (a on both,
¬intersect, g inside ABC since 0.5<1, f≠g), but the conclusion `between f g a` is FALSE (order is g-f-a).
In that config h (on ABC, `between f g h`, e.g. at dist 1 from f past g) is inside ADE with NO
contradiction, so `step_nhout_hin : False` is genuinely UNPROVABLE.

**VERIFIED FIX (needs human — signature is guarded by check_signatures):** add hypothesis
`|(g─a)| < |(f─a)|` (r_ADE < r_ABC ⟺ ADE is the inner circle) to `proposition_11`. This is the clean
discriminator: it excludes ABC-inner (r_ADE>r_ABC) and keeps ALL valid ADE-inner configs — including the
ones where f is inside ADE, which `¬f.insideCircle ADE` / `f.outsideCircle ADE` would WRONGLY exclude
(so those over-restrict and are unfaithful). With `|(g─a)|<|(f─a)|` added, step_nhout_hin builds
ZERO-sorry via the pf-construction (tested with a temporary diagnostic parameter — see step_nhout_hin.lean
header comment for the exact proof body).

Propagation of the fix: proposition_11 Main statement + the `have`s in step_nhout/step_nhout_hin (+ any
other step needing it) gain the binder; re-run check_signatures/check_steps --save (human). Prop13/step4
call `proposition_11 d g h ABDC EBFD` must then supply `|(h─d)| < |(g─d)|` (r_EBFD < r_ABDC), which holds
(EBFD is the inner circle) and is Main-suppliable. Cross-check Prop12 (external twin) which pins
orientation with `f.outsideCircle ADE ∧ g.outsideCircle ABC`.

## (superseded) earlier analysis: `step_nhout_hin` witness route
The hon route does NOT port. There `h'.outsideCircle ADE` was pinned by `|g-h|=|g-a|` (h on ADE). In hin
`|g-h| < |g-a|` so that metric is gone. Attempt (mirror of hon) TIMED OUT at 45s wall — and analysis
shows it is genuine **non-entailment**, not just timing:

- `h'.outsideCircle ADE` ⟺ `|g-h'| > |g-a| = r_ADE`.
- h' is the far FG∩ABC point; FG passes through centre f, so f is between h and h' (diameter through f):
  `|g-h'| = |g-f| + |f-h'| = |fg| + |f-a|` (since |f-h'|=|f-a|=r_ABC).
- `|g-a| ≤ |g-f|+|f-a| = |g-h'|` (triangle ineq), with **equality iff `between g f a`** — i.e. a lies on
  FG beyond f, i.e. **a = h'**. In that config h'=a is ON ADE, so `h'.outsideCircle ADE` is FALSE.
- `between g f a` is NOT ruled out by the hyps: `¬between f g a` (given) is a different order and is
  consistent with `between g f a`. So the witness route is not entailed.
- The degenerate `a=h'` (between g f a) forces `r_ADE = |fg|+r_ABC > r_ABC`, which OUGHT to be impossible
  under `¬ABC.intersectsCircle ADE` (inner circle would bulge outside the outer) — but that is a
  **circle-containment argument** euclid_finish does not find on its own.

## Recommended clean fix (needs a small proven helper, NOT an axiom)
Prove a positioning lemma and use it to collapse BOTH hon+hin:
  `h.onCircle ABC → h ≠ a → (a,ADE,ABC tangent-internally setup) → h.outsideCircle ADE`
i.e. "every point of the outer circle ABC other than the tangent point a is outside the inner ADE".
That is a genuine theorem (derivable, per CLAUDE.md it must NOT be an axiom). If it lands cheaply,
`step_nhout` reduces to the MAIN branch with no by_cases. The hard part is proving it in System E from the
intersection axioms (`intersection_circle_circle_1/2`) — the same containment difficulty, but proved once.

## Downstream impact
Book3/Prop13 (III.13) is **fully blocked** on III.11: Prop13/step4 cites III.11, and check_step's P
scan (`has_sorry` = ANY transitive `declaration uses 'sorry'`) fails while III.11 has sorries. Prop13/step4
itself is otherwise correct and builds.
