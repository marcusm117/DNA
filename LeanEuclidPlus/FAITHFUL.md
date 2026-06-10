# Making proofs faithful — human operator guide

**Goal:** make each Book-2 prop FAITHFUL — every Euclid sentence ↔ one checkable Lean step — and be
**mechanically certain** it's correct. Run everything from `LeanEuclidPlus/`; launch Claude from the
repo root `DNA/`. Each prop is a folder: `Book2/PropNN/Main.lean` (the proposition + its
`euclid_sentence`s) and `Book2/PropNN/stepN.lean` (one backing file per sentence, plus any
sub-files a hard step decomposes into).

**Why you can trust it (no LLM-trust for correctness).** Everything reduces to ONE operation on a
**node** (a named `:= by sorry` body — a sentence step or a `have`): *swap its sorry for its
`euclid_apply (helper…)`, build, revert.* If that builds, the node's hypotheses are **suppliable**;
if the node's backing file builds in isolation zero-sorry, it's **provable**. Both green for every
node (the `--all` audit, run bottom-up) ⟹ the final wired build **cannot fail** — Lean is the judge,
not the model. The ONLY human judgement is gate A: does each claim type match the English.

---

## ONE TIME (before any prop)
Snapshot the trusted statements so any later change to a `theorem proposition_*` is caught:
```
python3 scripts/check_signatures.py --save
```

## PER PROP (e.g. Prop04) — three phases, two human gates (▶)

**1. Phase A — translate (skill):**  `/faithful-map Book2/Prop04/Main.lean`
   Wipes the old proof; writes `Main.lean` = the (untouched) proposition signature + `euclid_intros`
   + the object-producing constructions + one `euclid_sentence "loc" "verbatim" (stepN : <claim>)
   := by sorry` per sentence + the intro/conclude bookends. **Every body is `:= by sorry`; no step
   files yet.** Elaborates cheap (all-sorry, SMT-free). STOPS for you.

**▶ 2. HUMAN GATE A — review + freeze the claims.**
   Read each claim type: does it honestly say what that Euclid sentence says? (The one thing no
   machine checks; use `Book2/data/diagrams/4.png` to resolve labels.) When happy:
   ```
   python3 scripts/check_steps.py --save Book2/Prop04/Main.lean
   ```

**3. Phase B — prove (skill):**  `/faithful-prove Book2/Prop04/Main.lean`
   The agent creates each `stepN.lean` and proves it, decomposing recursively (adding `have`+backing
   files) until every build is ≤30s. **Main stays all-sorry the whole time** — the agent never wires
   it; `check_step.py` does all wiring transiently and reverts. **Dev-state files import no pipeline
   (helper/step) files** — only `SystemE` + cited propositions; the script adds/removes a helper import
   alongside its wiring (this is why per-node checks are fast and isolated). The agent's last action is
   `check_step.py Book2/Prop04 --all` (exit 0). No human action needed mid-phase.

**▶ 4. HUMAN GATE B — re-run the audit.**
   ```
   python3 scripts/check_step.py Book2/Prop04 --all
   ```
   All ✓ (exit 0) ⟹ wiring everything is GUARANTEED to build. (Bottom-up; a failure names the
   deepest broken node.)

**5. Phase C — wire + verify (mechanical; YOU run it, not a skill):**
   ```
   python3 scripts/wire_main.py Book2/Prop04        # commits the wiring, strips 30s caps, builds once
   scripts/check_faithful.sh Book2                  # text (crit.1) + deps (crit.3), book-aware
   python3 scripts/check_steps.py Book2/Prop04/Main.lean   # claims unchanged since gate A
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
| `check_steps.py [--save] <Main>` | guard approved **claim types** (frozen after gate A) | human, gate A + gate C |
| `check_step.py <propdir> <node>` | certify one node: **SF** sufficient → **SP** suppliable → **P** provable (stops at first fail) | agent (Phase B) |
| `check_step.py <propdir> --sufficient/--suppliable/--provable <node>` | run just one of SF/SP/P (diagnostics; `--provable` reports remaining-sorry file:lines) | agent (Phase B) |
| `check_step.py <propdir> --provable` (no node) | build Main tolerating sorry — the Phase-A skeleton-elaborates check (Main has no parent ⟹ no SF/SP) | agent (Phase A) |
| `check_step.py <propdir> --context <node>` | print the real hypotheses available at a node | agent (Phase B) |
| `check_step.py <propdir> --check` | instant, no-build integrity scan (naming law, caps, no stray imports) | agent (Phase B) |
| `check_step.py <propdir> --all` | bottom-up audit (SP+P) of every node; exit 0 ⟹ Phase C guaranteed | agent (end of B) + human (gate B) |
| `wire_main.py <propdir> [--unwire]` | commit the wiring + build once (the ONLY script that keeps Main changed) | human (Phase C) |
| `check_faithful.sh Book2` | authoritative faithfulness (text + deps); needs a build first | human (gate C) |
| `safe_build.sh <target>` | serialized `lake build` (parallel-safe) | **human only** (agents are hard-denied raw builds; they use `check_step`) |

`check_step.py` (all Phase-B modes) NEVER leaves a file modified — every swap reverts atomically
(`git status` stays clean). Only `wire_main.py` (bare) commits the wiring; `--unwire` restores it.
The agent builds ONLY through `check_step`/`wire_main` (raw `lake build`/`safe_build.sh` are
hard-denied in `.claude/settings.json`); humans run `safe_build.sh` in their own terminal.

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
  naming law `node ≡ file ≡ helper_<book>_node`, a missing 30s cap, a pre-wired node). Fix the file.
- **`--all` SP-fail** → a node's hypotheses aren't suppliable by its container (or the build hit 30s).
  Fix that backing file's signature: drop the hyp / derive it in-body / hoist it to an earlier `have`;
  or decompose if it timed out. **Never raise a cap.**
- **`--all` P-fail** → a backing file doesn't build zero-sorry (a leaf with a `sorry`, a container with
  a sub-node/bare sorry, or a 30s timeout). Finish/decompose it.
- **Gate C build fails** → a step left unproven slipped through; `wire_main --unwire` and return to
  Phase B. `check_faithful.sh`/`check_steps.py`/`check_signatures.py` fail → a text/dep/claim/statement
  drifted; the message says which.
