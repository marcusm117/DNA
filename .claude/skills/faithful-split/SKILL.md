---
name: faithful-split
description: >
  Stage 1 of Phase A (faithful-split → faithful-map): split a Euclid proof's English text into ATOMIC
  assertions (a compound sentence becomes MULTIPLE entries — one per idea) and mark roles/justifications.
  TEXT-focused. Outputs an ORDERED JSON array to `Book<N>/PropNN/split.json` (NO `index` field — it's
  auto-assigned by array position). Invoked with a prop path, e.g. `/faithful-split Book2/Prop11`.
---

# Stage 1 — Split Euclid text into atomic assertions (TEXT-ONLY)

Your ONLY job: take the raw English text of a Euclid proposition and split it into atomic
assertions. You produce a JSON file. You do NOT translate to Lean, you do NOT look at any `.lean`
file, you do NOT open any diagram. This is pure English text analysis.

---

## HARD RULES

**RULE 1 — TEXT ONLY (one input file + one checker).** You read EXACTLY ONE input file:
`Book<N>/data/texts_proofs/<N>.txt` (Book 1 is flat: `Book/texts_proofs/<N>.txt`). **Read it DIRECTLY at
that exact path with the Read tool — do NOT search for it (there is NO `Glob`/`Grep` tool in this
harness).** You may NOT open ANY other file — no `.lean`, no diagrams, no `SystemE/`, no other props. The ONE script you MAY — and MUST —
run is the tiling gate `python3 scripts/check_faithful.py --split Book<N>/PropNN` (it reads only your
`split.json` + the canonical text, no codebase). Nothing else. If you feel the urge to "check" something
in the codebase — STOP. You have all the information you need in the text file + that gate.

**RULE 2 — VERBATIM TILING (WHITESPACE INCLUDED).** Your output slices, joined by EXACTLY ONE space
in index order, must reproduce the ENTIRE input text CHARACTER-FOR-CHARACTER — whitespace and all.
Nothing reworded, dropped, duplicated, or reordered. This is mechanically checked (byte-exact).

⚠ **WHITESPACE IS PART OF THE TEXT — do not tidy it.** The source (extracted from LaTeX) contains
runs of **multiple spaces**, both inside sentences (`same side,``  ``make`, `right-angles``  ``with`)
and at some sentence boundaries (`$CB$.``  ``For if`). The checker rejoins your slices with exactly
ONE space, so extra whitespace is YOUR responsibility:
  - **Inside a slice:** copy byte-for-byte — keep every double/triple space exactly as the file has it
    (a contiguous slice already preserves its own internal whitespace; never collapse it).
  - **At a boundary with >1 space between slices:** the single join-space covers ONE space; keep each
    EXTRA space as a TRAILING part of the left slice (or leading part of the right). E.g. source
    `…$CB$.``  ``For if…` → left slice ends `…$CB$. ` (trailing space), right slice `For if…` →
    join reproduces `…$CB$.``  ``For if…` ✓.
  Never normalize, collapse, or invent whitespace — reproduce exactly what the file has. A dropped
  boundary space is the #1 cause of a tiling FAIL.

**RULE 3 — ONE ATOMIC CLAIM PER ENTRY. A long/compound sentence becomes MULTIPLE entries.** Each entry
asserts ONE thing: one equality, one angle fact, one figure property, one construction action, one
"if X then Y" consequence, one contradiction. **Do NOT keep a multi-idea sentence as a single entry just
because it is one sentence** — that is the classic under-split mistake. When a sentence packs several
ideas — "$CB$ is equal to $GK$, and $CG$ to $KB$", or a reductio like "if the sides did not coincide,
then we would have the forbidden configuration … which is impossible" — SPLIT it at clause boundaries
into one entry per idea (the antecedent-consequence, each sub-fact, the contradiction). The ONLY limits:
each slice must stay a **clean contiguous span that tiles** (RULE 2), and you never merge across a
sentence boundary (RULE 4). If two facts are truly interleaved in one clause (no contiguous cut), only
then keep them in one entry.

**RULE 4 — ENTRY BOUNDARIES ARE ASSERTION BOUNDARIES, NOT PERIOD BOUNDARIES.** A period does NOT
automatically create a new entry. The test is: does the next sentence assert a NEW geometric fact,
or does it explain WHY the preceding claim holds? Euclid's punctuation (periods, commas) is a
formatting artifact — faithfulness is to what he ASSERTED, not where he put periods.
  - **Two genuine assertions always get separate entries** — but a "For…" / "For it is…" sentence
    that IMMEDIATELY follows a claim and gives its conditions/reason is NOT a new assertion. It stays
    in the SAME entry as the claim it justifies (Rule 5 takes precedence).
  - **The practical test**: if removing the "For…" sentence would leave the claim unproven-but-stated,
    and the "For…" sentence supplies the conditions under which the claim follows (the Prop citation,
    the equal-base/same-parallel conditions), then it's a justification — same entry.
  - **A new assertion:** "Thus, X is Y." / "And Z is W." — makes a claim that stands on its own.
    Always a new entry regardless of the preceding sentence.

**RULE 5 — JUSTIFICATIONS STAY WITH THEIR CLAIM — including across a period.** A "For..." or
"since..." or "for it is..." passage that gives the REASON for a claim stays in the same entry as
that claim. It is the justification, not a new assertion — regardless of whether Euclid put a period
before it. Mark the justification substrings as `assumption` spans within the merged entry.
  - **⚠ A "since X [Prop.~B.N]" clause is STILL a since-clause (an `assumption`) even when it carries
    its OWN proposition citation — the citation does NOT promote it to a standalone assertion.** The
    citation only records HOW that premise gets discharged downstream (an `@assumption` gap that Phase B
    proves via `[Prop.~B.N]`); it stays in the same entry as the "thus …" conclusion it feeds. So
    "since A [Prop.~1.34], but also B [Prop.~1.34], **thus** C [Prop.~1.30]" is **ONE deduction** — the
    single assertion is **C**, with A and B as two `assumption` spans (each keeping its `[Prop]` in the
    adjacent `glue`). Do NOT split it into three entries just because each clause is separately cited
    (real miss: I.45 "$FK$ equal+parallel $HG$ [1.34], but also $HG$ to $ML$ [1.34], $KF$ thus
    equal+parallel $ML$ [1.30]" — the two "since"/"but also" facts are the premises for the one "thus",
    exactly the two `proposition_34'` applies feeding the one `proposition_30` in the proof).

**RULE 6 — SEPARATE ASSERTION FROM ASSUMPTION; SPLIT COMPOUND ASSERTIONS (deductions).** Partition each
deduction's text into ordered `spans`, each labelled `assertion` (the ONE new fact — becomes the Lean
claim), `assumption` (a consumed prior fact — "because of X" / "since Y" — becomes an `@assumption`), or
`glue` (connectives, punctuation). Joined with NOTHING (empty string) the spans must reproduce the entry
text CHARACTER-FOR-CHARACTER — every weird/double/trailing space included (auto-checked by `--split`).
**If an `assertion` span bundles independent clauses (a comma or "and" — "…equal to…, at a different
point, on the same side"), SPLIT it into separate atomic entries** — UNLESS the clauses are interleaved
and cannot be sliced contiguously ("AB and AC … ED and DF"), in which case keep one entry. `--split`
WARNs on a compound assertion span; you make the final call.

---

## Roles

- **intro** — ALWAYS index 0. The opening block: the general enunciation ("If... then...") + the
  specific setup ("For let...") + the statement ("I say that..."). Everything from the start of the
  text up to (but not including) the first construction/deduction step.

- **construction** — "Let X be drawn/described/joined/produced..." — an action that creates a new
  geometric object. Note:
  - `construction_cite`: if `[Prop.~B.N]` appears, record `"B.N"` (e.g., `"1.46"`)
  - `objects_introduced`: the Euclid labels of new geometric objects (`["$CE$"]`, `["$ADEB$"]`)
  - `justifications`: **A CONSTRUCTION CAN HAVE A JUSTIFICATION TOO — don't skip it because the
    entry isn't a deduction.** A leading "For since X, let Y be constructed…" / "since X, let…" clause
    names a PRIOR FACT the construction consumes (the reason it is legal / possible) — mark it exactly
    like a deduction's justification: `"justifications": [{"substring": "…", "kind": "prior_fact"}]`.
    (Real miss: I.24.1 "For since angle $BAC$ is greater than angle $EDF$, let (angle) $EDG$ …
    have been constructed …" — the "angle $BAC$ is greater than angle $EDF$" clause is a consumed
    given and MUST be recorded, so faithful-map seeds it as an `@assumption`.) These become
    `@assumption` markers downstream just as a deduction's do.

- **deduction** — an assertion about a relationship or property (the bulk of the proof). Provide:
  - `spans`: the ordered `assertion`/`assumption`/`glue` partition of the sentence (RULE 6) — the
    primary structure. The `assumption` spans are the consumed prior facts ("because of X", "since Y").
  - `assertion`: a 1-line plain-English paraphrase of the new fact (human-readable summary).
  - `proof_cite`: if `[Prop.~B.N]` appears, record `"B.N"`.
  (The legacy `justifications` field is superseded by the `assumption` spans — omit it once you write `spans`.)

- **wts** ("what to show") — a MID-PROOF "I say that …" / "Again, I say that …" announcement of the
  goal (and its sub-parts "(That is) $AC$ to $DF$", "and $BC$ to $EF$", …). It states what the FOLLOWING
  sentences will prove — it is NOT itself a proven fact. Mark role `wts` and give ONLY `text` (no
  `spans`, no `assertion`, no `proof_cite`). The assembler stamps it as `euclid_wts` (a claimless
  structural tactic — the opening mirror of the trailing conclusion), so the map agent has no claim to
  fill. (The enunciation's OWN "I say that…" at the end of the text block is absorbed into `intro`,
  index 0 — `wts` is only for a mid-proof re-announcement, typically after "Again," in a second case.)

- **conclusion** — ALWAYS the last entry. The "Thus, if... then... (Which is) the very thing it
  was required to show." restatement.

## Reductio (proof-by-contradiction) frames — the `frame` overlay

A reductio has THREE text-signalled moves. Mark each with an optional `frame` object ON TOP OF its
normal role (these entries are still `deduction`s — they carry real claims: a disjunction, `False`, a
negation). The assembler uses them to stamp the nested `have habsurd<k> : ¬(…) := by intro …` block
automatically, so the map agent never hand-builds the frame — it only fills the `≠` type and adds any
`split_ors`/`wlog` the case structure needs.

- **reductio_open** — the "For if $AB$ is unequal to $DE$ …" / "For if not …" / "If possible, let …"
  sentence that SUPPOSES the negation of the goal. Record the supposed fact in `supposition` (the
  English of what is assumed for contradiction). The rest of the sentence ("… then one of them is
  greater") is still the entry's normal `assertion`/`spans`.
  ```json
  { "role": "deduction", "text": " For if $AB$ is unequal to $DE$ then one of them is greater.",
    "assertion": "one of them is greater",
    "frame": { "kind": "reductio_open", "supposition": "$AB$ is unequal to $DE$" },
    "spans": [ … ] }
  ```
- **contradiction** — "The very thing (is) impossible." (`assertion`: "contradiction"). The assembler
  pre-sets its claim to `False` and stamps the `exact` that closes the block.
  ```json
  { "role": "deduction", "text": "The very thing (is) impossible.", "assertion": "contradiction",
    "frame": { "kind": "contradiction" }, "spans": [ … ], "proof_cite": "1.16" }
  ```
- **reductio_close** — "Thus, $AB$ is not unequal to $DE$." — the sentence that DISCHARGES the reductio
  (establishes `¬supposition`, the block's result). `closes` is a **VERBATIM COPY of the matching
  open's `supposition`** — the two are linked by TEXT, not by any index number.
  ```json
  { "role": "deduction", "text": "Thus, $AB$ is not unequal to $DE$.", "assertion": "AB is not unequal to DE",
    "frame": { "kind": "reductio_close", "closes": "$AB$ is unequal to $DE$" }, "spans": [ … ] }
  ```
`check_faithful.py --split` cross-checks the triples: every `reductio_open` needs a later
`contradiction` and a later `reductio_close` whose `closes` copies its `supposition`. A prop with two
reductios (e.g. one per case, as in I.26) just has two open/contradiction/close triples.

---

## When to mark a justification

A justification is a substring that names a PRIOR FACT consumed by this step's reasoning:

**DO mark:**
- "since $AC$ is equal to $CE$" — cites a previously-established equality
- "for it is contained by $GB$ and $BC$" — cites a known containment relationship
- "$BG$ (is) equal to $A$" — at the end of a "For..." clause citing a prior step's result

**DO NOT mark:**
- The assertion itself (what THIS entry claims is true)
- "Similarly" / "for the same reasons" — too vague, skip
- Prop citations like "[Prop.~1.5]" — that goes in `proof_cite`, not justification

---

## Output format

Write a JSON array to `Book<N>/PropNN/split.json`, entries **IN ORDER** (intro first, then the steps,
conclusion last). **Do NOT write an `index` field — it is auto-assigned from array position** (position 0
= intro, 1, 2, … = steps, last = conclusion). You only keep the entries ordered; the numbering is
handled for you.

```json
{ "role": "intro", "text": "<verbatim contiguous slice of the input text>" }
```

For constructions, add `construction_cite` + `objects_introduced`:
```json
{ "role": "construction", "text": "...", "construction_cite": "1.46", "objects_introduced": ["$CDEB$"] }
```

For deductions, add `spans` (RULE 6) + a 1-line `assertion` paraphrase (+ `proof_cite` if `[Prop.~B.N]`):
```json
{ "role": "deduction",
  "text": "Therefore, since $AC$ is equal to $CE$, the angle $EAC$ is equal to the angle $AEC$.",
  "assertion": "angle EAC equals angle AEC",
  "spans": [
    { "label": "glue",       "text": "Therefore, since " },
    { "label": "assumption", "text": "$AC$ is equal to $CE$" },
    { "label": "glue",       "text": ", the " },
    { "label": "assertion",  "text": "angle $EAC$ is equal to the angle $AEC$" },
    { "label": "glue",       "text": "." } ],
  "proof_cite": "1.5" }
```
The span texts joined with NOTHING must equal `text` character-for-character (`--split` checks this).

Omit fields not relevant to a role. Use `null` for `construction_cite`/`proof_cite` when none is cited.

---

## Procedure

1. Read `Book<N>/data/texts_proofs/<N>.txt` (the ONLY file you read).
2. Identify the intro block (runs through "I say that...").
3. Identify the conclusion (the final "Thus, if... (Which is) the very thing...").
4. Split everything in between into atomic assertion entries.
5. Write the JSON array to `Book<N>/PropNN/split.json`.
6. VERIFY — MACHINE GATE (mandatory; run it, do NOT just eyeball). Run
   `python3 scripts/check_faithful.py --split Book<N>/PropNN`. It joins your slices with EXACTLY ONE
   space and compares BYTE-FOR-BYTE to the canonical text. On FAIL it names the exact char and shows the
   spot:
   - a **whitespace** miss → the source has a multi-space run your join dropped: add the missing
     space(s) INSIDE the adjacent slice (trailing the left / leading the right) per RULE 2, re-run.
   - a **word** divergence / missing tail / overrun → fix the slice text (verbatim, contiguous), re-run.
   **Loop until it prints `PASS`.** Do NOT stop, report, or hand off while it still FAILs — a split that
   doesn't tile poisons every downstream stage.
7. Report a summary table (index, role, first ~60 chars of text) and STOP for human review.

---

## Example (Prop 3, abbreviated)

Input text: "If a straight-line is cut at random... (Which is) the very thing it was required to show."

Output:
```json
[
  {"index": 0, "role": "intro", "text": "If a straight-line is cut at random, (then) the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the rectangle contained by (both of) the pieces, and the square on the aforementioned piece. For let the straight-line $AB$ be cut, at random, at (point) $C$. I say that the rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by $AC$ and $CB$, plus the square on $BC$."},
  {"index": 1, "role": "construction", "text": "For let the square $CDEB$ be described on $CB$ [Prop.~1.46],", "construction_cite": "1.46", "objects_introduced": ["$CDEB$"]},
  {"index": 2, "role": "construction", "text": "and let $ED$ be drawn through to $F$,", "construction_cite": null, "objects_introduced": ["$F$"]},
  {"index": 3, "role": "construction", "text": "and let $AF$ be drawn through $A$, parallel to either of $CD$ or $BE$ [Prop.~1.31].", "construction_cite": "1.31", "objects_introduced": ["$AF$"]},
  {"index": 4, "role": "deduction", "text": "So the (rectangle) $AE$ is equal to the (rectangle) $AD$ and the (square) $CE$.", "assertion": "rectangle AE equals rectangle AD plus square CE", "justifications": [], "proof_cite": null},
  {"index": 5, "role": "deduction", "text": "And $AE$ is the rectangle contained by $AB$ and $BC$. For it is contained by $AB$ and $BE$, and $BE$ (is) equal to $BC$.", "assertion": "AE is the rectangle contained by AB and BC", "justifications": [{"substring": "$BE$ (is) equal to $BC$", "kind": "prior_fact"}], "proof_cite": null},
  {"index": 6, "role": "deduction", "text": "And $AD$ (is) the (rectangle contained) by $AC$ and $CB$. For $DC$ (is) equal to $CB$.", "assertion": "AD is the rectangle contained by AC and CB", "justifications": [{"substring": "$DC$ (is) equal to $CB$", "kind": "prior_fact"}], "proof_cite": null},
  {"index": 7, "role": "deduction", "text": "And $DB$ (is) the square on $CB$.", "assertion": "DB is the square on CB", "justifications": [], "proof_cite": null},
  {"index": 8, "role": "deduction", "text": "Thus, the rectangle contained by $AB$ and $BC$ is equal to the rectangle contained by $AC$ and $CB$, plus the square on $BC$.", "assertion": "rectangle AB*BC = rectangle AC*CB + square BC", "justifications": [], "proof_cite": null},
  {"index": 9, "role": "conclusion", "text": "Thus, if a straight-line is cut at random, (then) the rectangle contained by the whole (straight-line), and one of the pieces (of the straight-line), is equal to the rectangle contained by (both of) the pieces, and the square on the aforementioned piece. (Which is) the very thing it was required to show."}
]
```

Note how entry 5 keeps "For it is contained by $AB$ and $BE$, and $BE$ (is) equal to $BC$." in the
same entry — it's the justification for "AE is the rectangle contained by AB and BC."
