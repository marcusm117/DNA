# Making proofs faithful — human operator guide

**Goal:** make each Book-2 prop FAITHFUL — every Euclid sentence ↔ one checkable Lean step — and be
**mechanically certain** it's correct. Run everything from `LeanEuclidPlus/`; launch Claude from the
repo root `DNA/`. Each prop is a folder: `Book2/PropNN/Main.lean` (the proposition + its
`euclid_sentence`s) and `Book2/PropNN/stepN.lean` (one backing file per sentence, plus any
sub-files a hard step decomposes into).

**Why you can trust it (no LLM-trust for correctness).** Everything reduces to ONE operation on a
**node** (a named `:= by sorry` body — a sentence step or a `have`): *swap its sorry for its
`euclid_apply (helper… (by assumption)…); (try split_ands) <;> assumption`, build, revert.* The helper
is FULLY applied — objects, then one `(by assumption)` per hypothesis, and the goal is closed
structurally (NOT `euclid_finish`) — so the wire does ZERO SMT: each hyp is a <1s core-Lean type-match
against the call-site context. If that builds, the node's hypotheses are all present (**suppliable**, SP).
A **leaf** backing file (no sub-`have`s) is **provable** (P) iff it builds in isolation zero-sorry; a
**container** (has sub-`have`s) is NOT re-built to prove it — instead its trailing tactics (the
`linarith [...]`/`euclid_finish` after the `have`s) are checked by building the container with sorries
tolerated (the SF-side build — SP does NOT run them; it stubs them to `sorry`), and its leaves by their
P. The `--all` audit = {SP every node} + {container build every container} + {P every leaf} +
{no stray sorry} ⟹ the final wired build **cannot fail** (every SMT query in it lives in a leaf body or
a container's trailing tactics, each already measured ≤30s; the wires themselves are SMT-free) — Lean is
the judge, not the model. The ONLY human judgement is gate A: does each claim type match the English.

---

## ONE TIME (before any prop)
Snapshot the trusted statements so any later change to a `theorem proposition_*` is caught:
```
python3 scripts/check_signatures.py --save
```
**Also build ALL dependencies once, so every cited olean is WARM:**
```
scripts/safe_build.sh Book Book2
```
This matters for speed AND robustness: with deps warm, a per-node `check_step` build compiles only
the target itself (≤30s), so the 30s wall never has to eat a cold dependency compile. It also makes
the interrupt self-heal exact — if a `check_step` build is wall-killed or Ctrl-C'd, `check_step` now
auto-purges THAT target's stale artifact (so its next build recompiles clean) without touching the
warm deps. The only case needing a manual `lake clean`/delete is the rare one where a *dependency*
itself was mid-compile at the kill — which warm deps prevent.

## PER PROP (e.g. Prop04) — three phases, two human gates (▶)

**1. Phase A — translate (skill):**  `/faithful-map Book2/Prop04/Main.lean`
   Wipes the old proof; writes `Main.lean` = the (untouched) proposition signature + `euclid_intros`
   + the object-producing constructions + one `euclid_sentence "loc" "verbatim" (stepN : <claim>)
   := by sorry` per sentence + the intro/conclude bookends. **Every body is `:= by sorry`; no step
   files yet.** Elaborates cheap (all-sorry, SMT-free). STOPS for you.

   **Sanity-check Criterion 1 (concatenated sentence texts == the canonical original) AND Criterion 4
   (every `-- @assumption ("text", …)` text is a substring of its sentence) — both must PASS:**
   - regex (quick, no build) — checks criterion 1 AND criterion 4:
   ```
   python3 scripts/check_faithful.py "Book2/Prop04/Main.lean"
   ```
   - olean (authoritative, book-aware):
   ```
   lake build Book2.Prop04.Main
   scripts/check_faithful.sh Book2.Prop04.Main
   ```

**▶ 2. HUMAN GATE A — review + freeze the claims (and record the @assumption map).**
   Read each claim type: does it honestly say what that Euclid sentence says? Also eyeball each
   `-- @assumption` line: is it a genuine *consumed input*, not a conjunct the step proves? (Both are
   human-checked — no machine fully verifies faithfulness; use `Book2/data/diagrams/4.png` to resolve
   labels.) When happy:
   ```
   python3 scripts/check_steps.py --save Book2/Prop04/Main.lean
   ```
   This freezes the claim TYPES **hard** and records the `@assumption` types. NOTE: the `@assumption`
   types are only Phase-A's best-guess reasoning map — Phase B may legitimately **drop/retype** a cited
   input the real call-site context shows isn't consumed, so `check_step --all` (and gate-C
   `check_steps.py`) report `@assumption` drift as a **non-blocking WARNING**, while claim-type drift
   stays a hard fail. If a Phase-B `@assumption` change is intended, just re-run `check_steps.py --save`
   to refreeze the map.

**3. Phase B — prove (skill):**  `/faithful-prove Book2/Prop04/Main.lean`
   The agent creates each `stepN.lean` and proves it, decomposing recursively (adding `have`+backing
   files) until every build is ≤30s. **Main stays all-sorry the whole time** — the agent never wires
   it; `check_step.py` does all wiring transiently and reverts. **Dev-state files import no pipeline
   (helper/step) files** — only `SystemE` + cited propositions; the script adds/removes a helper import
   alongside its wiring (this is why per-node checks are fast and isolated). Driving order: leaves first
   (`check_step <leaf>`) → confirm each container/step with `check_step --subtree <node>` (scoped to its
   cone) → `--all` ONCE at the very end. The agent's last action is `check_step.py Book2/Prop04 --all`
   (exit 0); it never runs `--all` mid-work. No human action needed mid-phase.

**▶ 4. HUMAN GATE B — re-run the audit.**
   ```
   python3 scripts/check_step.py Book2/Prop04 --all
   ```
   All ✓ (exit 0) ⟹ wiring everything is GUARANTEED to build. (Bottom-up; a failure names the
   deepest broken node.)

**5. Phase C — wire + verify (mechanical; YOU run it, not a skill):**
   **One command does all four (stops at the first failure):**
   ```
   scripts/phase_c.sh Book2/Prop04                  # = the four steps below, in order
   ```
   (or run them by hand — note the THREE different argument shapes, the slash-vs-dot footgun:)
   ```
   python3 scripts/wire_main.py Book2/PropNN        # commits the wiring, strips 30s caps, builds once
   scripts/check_faithful.sh Book2.PropNN.Main            # text (crit.1) + deps (crit.3), book-aware
   python3 scripts/check_steps.py Book2/PropNN/Main.lean   # claims unchanged since gate A
   python3 scripts/check_signatures.py              # no proposition statement was altered
   ```
   **▶ Gate C:** `wire_main` build green + zero sorry + all three checks PASS ⟹ Prop04 is faithful.
   (If the wired build fails: the fix is in a backing file → `wire_main.py Book2/Prop04 --unwire`
   returns Main to the all-sorry Phase-B state, then back to Phase B.)

---

## The scripts (who runs each)
| script | purpose | who |
|---|---|---|
| `check_signatures.py` `[--save]` | guard proposition **statements** (must never change) | human, once + gate C |
| `check_steps.py [--save] <Main>` | guard approved **claim types** (frozen-hard after gate A) + record the `@assumption` map (drift is a non-blocking WARNING — Phase B may drop/retype an input) | human, gate A + gate C |
| `check_step.py <propdir> <node>` | certify ONLY that one node (SF→SP→P, stops at first fail) — does NOT check its sub-nodes | agent (Phase B) |
| `check_step.py <propdir> --subtree <node>` | certify a node's WHOLE CONE (it + every sub-node it transitively contains), bottom-up, scoped — doesn't touch other steps; confirms a container/step is done | agent (Phase B) |
| `check_step.py <propdir> --sufficient/--suppliable/--provable <node>` | run just one of SF/SP/P (diagnostics; `--provable` reports remaining-sorry file:lines) | agent (Phase B) |
| `check_step.py <propdir> --provable` (no node) | build Main tolerating sorry — the Phase-A skeleton-elaborates check (Main has no parent ⟹ no SF/SP) | agent (Phase A) |
| `check_step.py <propdir> --context <node>` | print the real hypotheses available at a node | agent (Phase B) |
| `check_step.py <propdir> --smell <node>` | SM pre-decompose sanity check: fire the bare claim at `euclid_finish` (short solver cap) — "closes" ⟹ don't decompose / "not closed" ⟹ decompose / "SAT" ⟹ claim is false. Deliberate; the no-flag path does NOT run it | agent (Phase B) |
| `check_step.py <propdir> --check` | instant, no-build integrity scan (naming law, caps, no stray imports, no stray sorry, + criterion-3 deps) | agent (Phase B) |
| `check_step.py <propdir> --dependency` (`--deps`) | instant, no-build criterion-3 check, BOTH arms: every cited `[Prop.~B.N]` satisfied by a Main construction (`… as …`) OR its sentence's helper cone. Number-only; isolate fast before `--all` (which also runs it). The book-aware authority is the human's gate-C olean check — don't game it | agent (**Phase B** — needs helpers) |
| `check_step.py <propdir> --all` | WHOLE-prop bottom-up audit (SP every node + P every LEAF + no-stray-sorry + criterion-3 deps); the FINAL gate, run ONCE; exit 0 ⟹ Phase C guaranteed. Also surfaces `@assumption` drift as a non-blocking WARNING (does not affect exit code) | agent (end of B) + human (gate B) |
| `check_step.py <propdir> --whatchanged` (`--changed`) | instant, READ-ONLY (no build, no lock): after editing a file, report the MINIMAL set of certified nodes to re-check + WHY + the exact commands. Reads the certification manifest (written by `--all`/`--subtree`/each per-node PASS) and diffs input-file hashes. Use it instead of re-running `--all` after a fix | agent + human |
| `check_step.py <propdir> --status` (`--checklist`) | instant, READ-ONLY (no build, no lock, never writes): the durable RESUME BOARD — Main's own nodes (source order), each rolled up over its cone against the manifest into done/stale/todo, plus the 3 whole-prop checks (deps/integrity/orphans) + the exact NEXT `--subtree` commands. All-✓ + 3/3 ⟹ `--all` is GUARANTEED to pass. The committed mirror `PropNN/STATUS.md` is regenerated by `--all`/`--subtree`/per-node PASS (the same writers as the manifest) | agent + human |
| `check_step.py <propdir> --drive` | auto-loop `--subtree` over every Main node `--status` would report not-`done` (todo or stale), in source order, stopping at the first failure — covers cold-start (empty manifest) and warm-resume (skips already-`done` nodes) the same way, so you don't hand-drive `--status`'s printed command list yourself | agent (Phase B) |
| `wire_main.py <propdir> [--unwire]` | commit the wiring + build once (the ONLY script that keeps Main changed) | human (Phase C) |
| `phase_c.sh <propdir> [--unwire]` | run ALL of Phase C in order (wire_main → check_faithful → check_steps → check_signatures), stop at first failure; derives the dotted-module / Main.lean arg shapes for you | human (Phase C) |
| `check_faithful.py <Main>` | instant, no-build: text (crit 1, char-for-char) + construction-aware deps (crit 3, number-only — cited construction props need `… as …` in Main; proof-internal cites DEFER to Phase B) | agent (Phase A) |
| `check_faithful.sh Book2.PropNN.Main` | authoritative faithfulness (text crit.1 + deps crit.3, BOOK-AWARE); needs a build first. Deps are TWO-ARM, mirroring `--dependency`: each cited `[Prop.~B.N]` resolves via a Main construction (`… as …`, whole-Main) OR the citing sentence's helper cone — matched by the compiler-resolved (book-authenticated) name. Pass the `.Main` submodule (where the sentences live), or `Book2` to check every prop at once | human (gate C) |
| `safe_build.sh <target>` | serialized `lake build` (parallel-safe) | **human only** (agents are hard-denied raw builds; they use `check_step`) |

`check_step.py` (all Phase-B modes) NEVER leaves a `.lean` file modified — every swap reverts
atomically (`git status` stays clean). (The audit modes do write one git-ignored bookkeeping file —
the certification manifest under `.lake/faithful-certified/<prop>.json`, read by `--whatchanged`;
it's invisible to git and to every `.lean` check.) Only `wire_main.py` (bare) commits the wiring;
`--unwire` restores it.
The agent builds ONLY through `check_step`/`wire_main` (raw `lake build`/`safe_build.sh` are
hard-denied in `.claude/settings.json`); humans run `safe_build.sh` in their own terminal.

**What you may see (shared helpers).** A `have` helper reused by several sentences shows in `--all` as
`name: SP [N call sites] + P` (suppliability checked at each parent, proof built once). If it's reused
on *different* objects per site, each call carries a `-- @args: …` comment line above it naming that
site's actuals — committed and harmless (the guards ignore comments). Nothing for you to do; it's the
agent's mechanism for generic reuse.

**Convention — `Main` is NOT a node.** Nodes are the `euclid_sentence`s *inside* Main and the `have`s;
each has a backing file, a claim, and a parent. Main is the root container — no backing file, no
parent — so it has no SF/SP, only a build. Therefore: build Main with `check_step <propdir> --provable`
(NO node); never pass `Main` as a node (SF/SP/bare with `Main` or with no node FAIL with a message
pointing here). `propdir_of` requires `Main.lean` to exist, so a prop with no Main is rejected up front.

## Running many in parallel
One agent per prop folder; approve each at gate A independently. Book 1 (`Book/`, flat) is untouched.

## If a gate fails — what it means / where to fix
- **Gate A** never "fails" — it's your judgement. If a claim is wrong, fix it in `Main.lean` and
  re-`--save`.
- **`--check` fails** → a structural problem (a node with no backing file, a name that breaks the
  naming law `node ≡ file ≡ helper_<book>_<prop>_node`, a missing 30s cap, a pre-wired node). Fix the file.
- **`--all` SP-fail** → a hypothesis the node declares isn't present at its call site, so its
  `(by assumption)` failed (`tactic 'assumption' failed`) — the wire is SMT-free, so this is NOT a
  timeout, it's a signature mismatch. Fix that backing file's signature: drop the hyp and derive it
  in-body (`euclid_assert` before use), or match its form to the literal atom the context has (take the
  atoms of a packaged abbrev, fix an orientation). **Never raise a cap** (caps are irrelevant here).
  (If the *combine* above the node times out instead, that's a P/combine cost — decompose it.)
- **`--all` P-fail** → a LEAF backing file doesn't build zero-sorry (still has a `sorry`, or a 30s
  timeout → decompose into more `have`+backing files). Containers aren't P-built.
- **`--check` stray-sorry** → a `sorry`/`admit`/`axiom` that isn't a declared node body (e.g. a faked
  combine). Replace with real tactics (`euclid_finish`), or make it a proper `have`+backing node.
- **Gate C build fails** → a step left unproven slipped through; `wire_main --unwire` and return to
  Phase B. `check_faithful.sh`/`check_steps.py`/`check_signatures.py` fail → a text/dep/claim/statement
  drifted; the message says which.

## After editing a file mid-proof — `--whatchanged` (don't re-run `--all` to find out)
Once you've run an audit (`--all`, or any `--subtree`/per-node check), a **certification manifest**
records which nodes are proven and the hashes of each node's *input files*. When you then edit a file
to fix something, run:
```
python3 scripts/check_step.py Book2/Prop04 --whatchanged
```
It diffs the hashes and prints the **minimal, exact** set of nodes to re-check — never a guess, never
the whole prop:
```
CHANGED FILES:  • Book2/Prop04/step24.lean (modified)
MUST RE-CHECK (1 node):  ✗ step24_hf — it is wired in step24.lean, which modified → re-run SP
Still certified (unaffected): 46 node(s).
RE-CHECK COMMANDS:  python3 scripts/check_step.py Book2/Prop04 step24_hf
```
**Why this is the whole story (sound + minimal):** the SF/SP/P checks are mutually isolated, so a
node's certificate depends ONLY on its own input files — its backing file + the container(s) it's wired
in. Editing file X therefore invalidates exactly `{the node backed by X} ∪ {the nodes wired inside X}`
and nothing else — there is **no transitive cascade** (a grandparent builds against the parent's
signature in `parent.lean`, which you didn't touch). So a node NOT listed is still genuinely certified.
Re-running `check_step <node>` on each listed node re-stamps its hashes (clearing it from
`--whatchanged`); once all pass, run `--all` ONCE as the final witness. `--whatchanged` itself is
read-only — no build, no lock, never edits anything.

## Resuming work — `--status` (the durable checklist)
Phase B on a real prop spans many sessions/agents. `--status` is the board you check FIRST when
picking a prop back up — it answers "what's left" without re-deriving it from memory or re-running
`--all`:
```
python3 scripts/check_step.py Book2/Prop04 --status
```
It walks **Main's own nodes, in true source order** (every `euclid_sentence` and every top-level
`have` literally in `Main.lean` — not their sub-nodes), and rolls each one's whole cone up against
the certification manifest into exactly one of:
```
✓ step7   done   cone certified, inputs fresh
⚠ step12  stale  Book2/Prop04/step12.lean changed since audit (re-run: --subtree step12)
○ step20  todo   cone has uncertified node(s): step20_hbc, step20_par
```
plus the 3 whole-prop checks (criterion-3 deps / integrity / orphans) and a `SUMMARY` line with the
exact next `--subtree`/`--all` command. **Drive Main's nodes in this order, top to bottom** — once a
node shows `✓`, it's done; never revisit an earlier `✓` node except by editing inside its own cone
(which immediately flips it back to `⚠` via the hash check, so you can't silently regress it).
**All-✓ + all 3 checks green ⟺ `--all` is guaranteed to pass** — `--status` IS `--all`'s outcome,
computed read-only from the manifest instead of re-running the audit.

`--status` is read-only (no build, no lock, never writes anything) — safe to run any time, including
mid-build by another process. To actually CLOSE what `--status` lists instead of running each printed
`--subtree` command by hand, run `--drive`: it takes the same rollup, runs `--subtree` on the first
not-`done` node, stops at the first real failure (fix it, then re-run `--drive` to resume), and
otherwise keeps going until every Main node is `✓`. It works the same way on a prop with NO manifest
yet (every node starts `todo`, so it just drives node 1, 2, 3, … in order) as it does resuming a
partially-certified prop (it skips the already-`done` nodes).

The **committed mirror** `PropNN/STATUS.md` is a plain rendering of the
same rows, regenerated automatically by whatever already writes the manifest (`--all`, `--subtree`,
each per-node PASS) — so it's always at most one audit stale, is reviewable in a diff/PR, and (like
`agent_notes.md` below) is invisible to every `.lean` scanner. **Never hand-edit `STATUS.md`** — it's
overwritten on the next audit; if it looks wrong, the manifest or the rows are wrong, not the file.

**Freeform notes alongside the checklist.** Two `.md` scratchpads (never parsed back, never enforced,
just for agents/humans to leave breadcrumbs):
- `AGENT_NOTES.md` (repo root) — cross-cutting findings: tooling quirks, token-savers, ideas that
  span props.
- `Book<N>/PropNN/agent_notes.md` (per-prop, created on demand) — findings scoped to that one prop:
  why a node was decomposed a certain way, a dead end you tried, context the next agent on this prop
  should have. Check it when resuming a prop, alongside `--status`.
