---
name: faithful-split
description: >
  Stage 1 of the faithful-map pipeline: split a Euclid proof's English text into atomic assertions
  and mark roles/justifications. TEXT-ONLY — no Lean, no diagram, no codebase reading. Outputs JSON
  to `Book<N>/PropNN/split.json`. Invoked with a prop path, e.g. `/faithful-split Book2/Prop11`.
---

# Stage 1 — Split Euclid text into atomic assertions (TEXT-ONLY)

Your ONLY job: take the raw English text of a Euclid proposition and split it into atomic
assertions. You produce a JSON file. You do NOT translate to Lean, you do NOT look at any `.lean`
file, you do NOT open any diagram. This is pure English text analysis.

---

## HARD RULES

**RULE 1 — TEXT ONLY.** You may read EXACTLY ONE file: `Book<N>/data/texts_proofs/<N>.txt`. You may
NOT open ANY other file — no `.lean` files, no diagrams, no `SystemE/`, no `scripts/`, no other
props. If you feel the urge to "check" something in the codebase — STOP. You have all the
information you need in the text file.

**RULE 2 — VERBATIM TILING.** Your output slices, joined by single spaces in index order, must
reproduce the ENTIRE input text CHARACTER-FOR-CHARACTER. Nothing reworded, dropped, duplicated, or
reordered. This is mechanically checked.

**RULE 3 — ONE ATOMIC CLAIM PER ENTRY.** Each entry asserts ONE thing: one equality, one angle
fact, one figure property, one construction action. If a sentence packs multiple claims ("$CB$ is
equal to $GK$, and $CG$ to $KB$"), SPLIT at a clause boundary into separate entries. But ONLY if
the split produces clean contiguous slices that tile. If not (interleaved facts in one clause),
keep as one entry with both facts.

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

Write a JSON array to `Book<N>/PropNN/split.json`. Each element:

```json
{
  "index": 0,
  "role": "intro",
  "text": "<verbatim contiguous slice of the input text>"
}
```

For constructions, add:
```json
{
  "index": 1,
  "role": "construction",
  "text": "...",
  "construction_cite": "1.46",
  "objects_introduced": ["$CDEB$"]
}
```

For deductions, add:
```json
{
  "index": 5,
  "role": "deduction",
  "text": "...",
  "assertion": "angle EAC equals angle AEC",
  "justifications": [
    {"substring": "$AC$ is equal to $CE$", "kind": "prior_fact"}
  ],
  "proof_cite": "1.5"
}
```

Omit fields not relevant to a role (don't include `construction_cite` on deductions, etc.).
Use `null` for `construction_cite`/`proof_cite` when no proposition is cited.

---

## Procedure

1. Read `Book<N>/data/texts_proofs/<N>.txt` (the ONLY file you read).
2. Identify the intro block (runs through "I say that...").
3. Identify the conclusion (the final "Thus, if... (Which is) the very thing...").
4. Split everything in between into atomic assertion entries.
5. Write the JSON array to `Book<N>/PropNN/split.json`.
6. VERIFY: mentally reconstruct text by joining all `text` fields with spaces — it MUST equal the
   original char-for-char. If not, fix your splits.
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
