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

**RULE 4 — NEVER MERGE ACROSS SENTENCES.** A period boundary (end of sentence) is ALWAYS at least
an entry boundary. Two sentences never become one entry.

**RULE 5 — TRAILING JUSTIFICATIONS STAY.** A "For..." or "since..." or "for it is..." clause that
gives the REASON for a claim stays in the same entry as that claim. It's the justification, not a
new assertion.

---

## Roles

- **intro** — ALWAYS index 0. The opening block: the general enunciation ("If... then...") + the
  specific setup ("For let...") + the statement ("I say that..."). Everything from the start of the
  text up to (but not including) the first construction/deduction step.

- **construction** — "Let X be drawn/described/joined/produced..." — an action that creates a new
  geometric object. Note:
  - `construction_cite`: if `[Prop.~B.N]` appears, record `"B.N"` (e.g., `"1.46"`)
  - `objects_introduced`: the Euclid labels of new geometric objects (`["$CE$"]`, `["$ADEB$"]`)

- **deduction** — An assertion about a relationship or property. This is the bulk of the proof.
  Identify:
  - `assertion`: plain English paraphrase of what is being claimed (1 sentence)
  - `justifications`: any "since X", "for X", "X being equal to Y" substrings that cite a PRIOR
    fact as the REASON for this assertion. Each must be a VERBATIM CONTIGUOUS SUBSTRING of the
    entry's text. Only mark substrings that name a prior fact the step CONSUMES — not the
    assertion itself.
  - `proof_cite`: if `[Prop.~B.N]` appears, record `"B.N"`

- **conclusion** — ALWAYS the last entry. The "Thus, if... then... (Which is) the very thing it
  was required to show." restatement.

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

For deductions, add `assertion` + `justifications` (+ `proof_cite` if a `[Prop.~B.N]` is cited):
```json
{ "role": "deduction", "text": "...",
  "assertion": "angle EAC equals angle AEC",
  "justifications": [ {"substring": "$AC$ is equal to $CE$", "kind": "prior_fact"} ],
  "proof_cite": "1.5" }
```

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
