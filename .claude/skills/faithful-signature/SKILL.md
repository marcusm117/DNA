---
name: faithful-signature
description: >
  Phase A, stage 0 for Book 3 (and any book whose propositions have no pre-existing Lean statement):
  translate a proposition's ENUNCIATION into its Lean `theorem proposition_N` signature (binders +
  given hypotheses + goal) and write a `Book<N>/PropNN/Main.lean` STUB (header + `:= by sorry`).
  TRANSLATION ONLY — not proving, not the proof body (that is faithful-map). References the Book-3
  vocabulary primer so every prop is rendered identically. Invoked with a prop path, e.g.
  `/faithful-signature Book3/Prop02`.
---

# Phase A · Stage 0 — Write the proposition SIGNATURE (enunciation → theorem statement)

Your ONLY job: turn the ENUNCIATION of one proposition into its Lean theorem statement —
`theorem proposition_N : ∀ (binders), <given hyps> → <goal>` — and write a minimal, self-contained
`Book<N>/PropNN/Main.lean` stub whose body is `:= by sorry`. You do NOT prove anything and you do NOT
write the proof body's `euclid_sentence` steps (that is `faithful-map`, a later stage).

Books 1 and 2 skipped this stage because their propositions already existed in `Book/`. Book 3 has no
Lean statements, so the signature is a genuine translation step — and the highest-stakes one: if the
statement's given/goal is wrong, every downstream sentence is faithful to the WRONG theorem.

---

## What you read

1. **The enunciation.** Prefer `Book<N>/PropNN/split.json` **index 0** (`intro`) — the opening block
   (general enunciation + "Let ABC be…" setup + "I say that…"). If `split.json` does not exist yet,
   read the opening block of `Book<N>/data/texts_proofs/<N>.txt` directly (up to the first
   construction/deduction). This is the ONLY source of the statement's content.
2. **The vocabulary primer — REQUIRED:** `NOTES/BOOK3_VOCAB_PRIMER.md`. Every circle word maps through
   it (native predicate or inline convention). Do not invent a rendering it doesn't sanction.
3. **The diagram** `Book<N>/data/diagrams/<N>.png` — for **LABEL RESOLUTION ONLY** (which point is the
   center, which letters name the circle). NEVER read a fact off the diagram into the statement; the
   statement comes from the enunciation TEXT.

Do NOT read other `.lean` files, `SystemE/`, or other props. The primer + enunciation are sufficient.

---

## How to build the statement

**Binders** — one per distinct Euclid label in the enunciation, typed:
- points → lowercase (`A → a`); lines → uppercased label (`AB → AB : Line`); circles → the label as an
  uppercase identifier (`ABC : Circle`), per the primer's naming rules.
- A circle "named ABC" is pinned by three points on it: introduce `a b c : Point` + `ABC : Circle` with
  `a.onCircle ABC ∧ …`. Only introduce labels the enunciation actually names.

**Given hypotheses** (left of the `→`) — the setup facts: incidence (`onCircle`/`onLine`/`isCentre`),
betweenness, distinctness, "through the center" / "not through the center", equalities the enunciation
states as given. Use the primer's conventions (`touches` inline, "circumference"=locus→`onCircle`, etc.).

**Goal** (right of the `→`) — translate "I say that…". Match the shape (primer §Goal shapes):
- **construction** ("To find…/draw…/cut off…") → existential `∃ <obj>, <properties>`.
- **property/theorem** → the property or equality, no `∃`.
- **biconditional** ("…and conversely…") → `(P → Q) ∧ (Q → P)` (or the two implications as phrased).

When a choice is genuinely ambiguous (which side, minor vs major arc, how to pin a constructed object),
pick the primer-sanctioned default and FLAG it in your report for the operator — do not silently guess.

---

## What you write

`Book<N>/PropNN/Main.lean`, exactly this shape (nothing else — no `euclid_sentence`, no steps):

```lean
import SystemE

namespace Elements.Book3

theorem proposition_N : ∀ (<binders>),
  <given hyps> →
  <goal> :=
by
  sorry
```

- `N` = the proposition number (Prop02 → `proposition_2`).
- **`import SystemE` only, and NO `open Elements.Book1`.** The statement cites no Book-1 lemma, and with
  only `import SystemE` the `Elements.Book1` namespace isn't populated — an `open` would fail with
  "unknown namespace". The `open` + any cited-prop imports are added LATER by the map/assemble step.
- **Introduce ONLY the points the statement uses.** A given circle is just `ABC : Circle`; do NOT force
  three `_.onCircle` naming points onto it. No dead hypotheses (see primer §Naming conventions).
- Body is `by\n  sorry`. The `faithful_map_assemble` step later preserves this signature byte-for-byte
  and overwrites only the body, so your header must be final and correct.

**Then VERIFY it compiles** — run `python3 scripts/check_step.py Book<N>/PropNN --signature` (builds the
bare stub, tolerating the lone `sorry`, and confirms every predicate/notation/identifier resolves). It
must print `OK: the signature elaborates.` If it FAILs, read the Lean error and fix the statement
(unknown identifier → wrong predicate name; unknown namespace → stray `open`; type mismatch → wrong
argument). Do NOT report a signature that doesn't compile. (Run BARE from the repo root — no `cd`, no pipe.)

---

## Report and STOP (human review)

End by reporting, for the operator to review:
1. The full `theorem proposition_N …` you wrote.
2. A line-by-line **enunciation → Lean** mapping: each binder, each hypothesis, the goal — quoting the
   English phrase each came from.
3. Any **FLAGS**: ambiguous modeling choices, arc/segment/tangent conventions applied, a construction's
   existential pinning, anything you defaulted.

Then STOP. The operator reviews the statement and, once approved, runs `check_signatures --save` to
register the Book-3 baseline (that command is human-only — never attempt it).

---

## Hard rules

- **Statement from the TEXT, not the diagram.** Diagram resolves labels only.
- **Primer is authoritative** for every circle word. No new `def`, no rendering the primer doesn't list.
- **Signature only.** No proof body, no `euclid_sentence`, no proving. Body stays `sorry`.
- **Flag, don't guess.** A genuine modeling ambiguity gets the primer default + a FLAG, never a silent choice.
- **One prop per invocation.** You translate exactly the prop named in the path.
