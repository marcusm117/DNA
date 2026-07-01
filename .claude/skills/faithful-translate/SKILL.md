---
name: faithful-translate
description: >
  Stage 2 of the Phase-A sentence-map pipeline (faithful-split → faithful-translate →
  faithful_map_assemble.py): translate each atomic assertion from split.json into a Lean
  claim type, using ONLY the diagram + the vocabulary sheet below + the prop signature. NO codebase
  reading beyond the prop signature. Outputs `Book<N>/PropNN/translate.json`. Invoked with a prop
  path, e.g. `/faithful-translate Book2/Prop11`.
---

# Stage 2 — Translate assertions to Lean claim types (DIAGRAM + VOCAB ONLY)

Your job: take the `split.json` produced by `/faithful-split` and translate each assertion into a
Lean claim type. You have three inputs and NOTHING ELSE:
1. The `split.json` file (atomic assertions with roles and justifications)
2. The diagram image (`Book<N>/data/diagrams/<N>.png`) — for label resolution
3. The proposition signature from `Main.lean` — ONLY the `theorem proposition_N : ∀ (...) ...` line
   (tells you existing variable names and the conclusion type)

---

## HARD RULES

**RULE 1 — RESTRICTED READING.** You may read EXACTLY:
- `Book<N>/PropNN/split.json`
- `Book<N>/data/diagrams/<N>.png`
- `Book<N>/PropNN/Main.lean` — ONLY to extract the theorem signature (the `∀ (a b c : Point)...`
  header and conclusion)
- **Cited construction prop signatures:** For each `construction_cite` in split.json (e.g. "1.46",
  "1.31"), you may read that prop's Main file (`Book/Prop46.lean` for Book 1, or
  `Book2/PropNN/Main.lean` for Book 2) — ONLY the theorem signature line, to see what arguments it
  takes and what objects/properties it returns. This tells you the construction call pattern.

You may NOT open: `SystemE/`, `scripts/`, `Helpers/`, step files, or any prop file NOT cited as a
construction in split.json. Everything else you need is in the VOCABULARY below + the diagram.

**RULE 2 — THE SENTENCE IS THE CLAIM.** Translate what the sentence SAYS, not what you think it
implies or what would help prove it. If Euclid says "angle EAC equals angle AEC", your claim is
`∠ e:a:c = ∠ a:e:c` — period. Don't expand it into unstated facts.

**RULE 3 — USE ONLY THE VOCABULARY BELOW.** If you think you need a Lean construct not listed
here, you're wrong — re-read the sentence. The vocabulary covers everything Book 2 needs.

---

## VOCABULARY (everything you can use in claim types)

### Lengths and products
```
|(a─b)|                    -- length of segment from point a to point b
|(a─b)| * |(c─d)|         -- "the rectangle contained by AB and CD"
|(a─b)| * |(a─b)|         -- "the square on AB" (length squared)
```

### Angles
```
∠ a:b:c                   -- angle at vertex b, rays b→a and b→c
∟                          -- right angle constant
∠ a:b:c = ∟               -- "angle ABC is a right angle"
∠ a:b:c = ∟ / 2           -- "half a right angle"
∠ a:b:c + ∠ d:e:f = ∟ + ∟ -- "sum equals two right angles"
∠ a:b:c + ∠ d:e:f < ∟ + ∟ -- "sum is less than two right angles"
∠ a:b:c = ∠ d:e:f         -- "angle ABC equals angle DEF"
```

### Areas (figures as triangle sums)
```
Triangle.area △ p:q:r      -- area of triangle with vertices p, q, r

-- A quadrilateral ABCD (named by opposite corners) = two triangles:
Triangle.area △ a:b:c + Triangle.area △ a:c:d

-- "rectangle BH" (named by opposite corners B,H with other corners G,C):
Triangle.area △ b:c:h + Triangle.area △ b:g:h
```

### Incidence and order
```
p.onLine L                 -- point p lies on line L
between a b c              -- b is between a and c on their shared line
¬(L.intersectsLine M)     -- L is parallel to M (lines don't intersect)
p.sameSide q L             -- p and q on the same side of line L
p.opposingSides q L        -- p and q on opposite sides of line L
```

### Relations
```
formParallelogram a b c d AB CD AC BD  -- ABCD is a parallelogram on those lines
formTriangle a b c AB BC AC            -- ABC is a triangle on those lines
distinctPointsOnLine a b L             -- a ≠ b and both on L
parallelLines L M                      -- (alternative: ¬(L.intersectsLine M))
```

### Connectives
```
∧                          -- conjunction: claim1 ∧ claim2
```

### Construction calls (for construction-role entries)

When an entry has role "construction", you specify what Lean call produces the object. READ THE
CITED PROP'S SIGNATURE to get the exact argument order and output tuple. Common infrastructure:

```
-- "let AB be joined" (no prop citation — just line_from_points)
line_from_points a b           → AB

-- intersection point (when two lines meet — no prop citation)
intersection_lines L M         → p (the intersection point)

-- "let it be made equal to X" [Prop.~1.3] — requires extend first:
line_from_points c e0          → CE
extend_point_longer CE c e0 (a─c) → e1
proposition_3 c e1 a c CE L    → e (point at distance |AC| from C on CE)
```

For cited constructions (`[Prop.~1.46]`, `[Prop.~1.31]`, `[Prop.~1.11]`, etc.), read the cited
prop's signature to determine: argument order, output variables, and what properties they deposit.
The signature tells you exactly what to write.

### Variable naming conventions
- Points: lowercase single letters (`a`, `b`, `c`, `d`, `e`, `f`, `g`, `h`)
- Lines: UPPERCASE, often two-letter (`AB`, `CE`, `GH`, `FD`)
- The proposition signature already names the GIVEN points/lines — use those exact names
- For NEW points from constructions, use lowercase. Follow the Euclid label:
  `$E$` → `e`, `$G$` → `g`, `$F$` → `f`
- When a construction needs intermediate points (like `e0`, `e1` before getting `e`),
  use numbered variants: `e0`, `e1`, then the final `e`

---

## ASSUMPTION TRANSLATION

For each justification marked in `split.json`, translate the substring to a Lean type:

- The justification `"$AC$ is equal to $CE$"` → lean_type `|(a─c)| = |(c─e)|`
- The justification `"$BG$ (is) equal to $A$"` → lean_type `|(b─g)| = |(a₁─a₂)|`

**INPUTS-ONLY rule:** Only translate justifications that name a PRIOR fact this step CONSUMES.
If the justification substring is actually stating what THIS entry claims (it's the assertion
itself), do NOT include it in `assumptions` — it belongs in the claim.

---

## Output format

Write a JSON array to `Book<N>/PropNN/translate.json`. Each element:

```json
{
  "index": 1,
  "step_name": "step1",
  "role": "construction",
  "text": "<carried from split.json>",
  "lean_claim": "∠ a:c:e = ∟",
  "construction": {
    "calls": [
      {"call": "proposition_11 a b c AD", "as": "e0"},
      {"call": "line_from_points c e0", "as": "CE"},
      {"call": "extend_point_longer CE c e0 (a─c)", "as": "e1"},
      {"call": "proposition_3 c e1 a c CE AC'", "as": "e"}
    ]
  },
  "assumptions": []
}
```

For deductions:
```json
{
  "index": 5,
  "step_name": "step5",
  "role": "deduction",
  "text": "And since $AC$ is equal to $CE$, angle $EAC$ is also equal to (angle) $AEC$ [Prop.~1.5].",
  "lean_claim": "∠ e:a:c = ∠ a:e:c",
  "assumptions": [
    {"substring": "$AC$ is equal to $CE$", "lean_type": "|(a─c)| = |(c─e)|"}
  ]
}
```

For intro/conclusion entries, carry them through with no claim:
```json
{
  "index": 0,
  "role": "intro",
  "text": "...",
  "lean_claim": null
}
```

**step_name numbering:** Skip intro (index 0) and conclusion (last index). Number the rest as
`step1`, `step2`, ... in order. So index 1 → `step1`, index 2 → `step2`, etc.

---

## Procedure

1. Read `Book<N>/PropNN/split.json`.
2. Read the diagram `Book<N>/data/diagrams/<N>.png` — use it to resolve labels (which point is
   where, which corners a figure name denotes, vertex ordering).
3. Read `Book<N>/PropNN/Main.lean` — extract ONLY the theorem signature line(s) to get the
   existing variable names and conclusion.
4. For each entry in split.json:
   - If intro/conclusion: carry through with `lean_claim: null`
   - If construction: write the `lean_claim` (the defining property the construction establishes)
     + the `construction.calls` array (the sequence of Lean calls that produce the objects)
   - If deduction: write the `lean_claim` + translate any justifications to `assumptions`
5. Write to `Book<N>/PropNN/translate.json`.
6. Run the GATE-A self-review below, fix anything it flags, THEN report a summary table and STOP for
   human review.

---

## GATE-A SELF-REVIEW (run before you STOP — these are the exact issues humans keep catching)

Pass over your own `translate.json` and confirm each box. This is the reviewer wisdom salvaged from
the old monolithic Phase-A skill; it is load-bearing for faithfulness:

  □ No `null`/`True`/vacuous claim on any non-structural entry — no definitional tautology
    (`|(a─b)| = |(b─a)|`, `x = x`) that holds regardless of the geometry. Every deduction/construction
    asserts something; state THAT. (Only intro/conclusion carry `lean_claim: null`.)
  □ Every `assumptions` entry: (a) its `substring` is a verbatim substring of the entry text; (b) its
    `lean_type` is a genuine INPUT the step CONSUMES — NOT a conjunct of the step's own claim. If
    unsure, DROP it — the INPUTS-ONLY rule is load-bearing.
  □ No construction-byproduct incidences in any `lean_claim` — only what the sentence asserts, not the
    extra `.onLine`/intersection facts a construction happens to deposit.
  □ Every figure-area claim uses the figure's REAL corners (from the diagram); no region double-counted
    or omitted.
  □ No claim expanded into facts the text didn't state — one entry → its one atomic idea; never invent.
  □ Each `text` is carried through verbatim from `split.json` (unchanged, not reworded).
  □ You did NOT open any `SystemE/Theory/Inferences/**` (or any file outside the allowed set) — writing
    a claim from axioms is proving, not translating.

---

## Common claim patterns (sentence shape → claim shape)

| Euclid says | Lean claim |
|---|---|
| "angle ABC is a right angle" | `∠ a:b:c = ∟` |
| "angle ABC equals angle DEF" | `∠ a:b:c = ∠ d:e:f` |
| "AB is equal to CD" (lengths) | `|(a─b)| = |(c─d)|` |
| "the square on AB equals..." | `|(a─b)| * |(a─b)| = ...` |
| "X is the rectangle by A and B" | `area(figure) = |(a─...)| * |(b─...)|` (use triangle sums for area) |
| "rectangle AE = rectangle AD + square CE" | triangle-sum equation |
| "EAC and AEC are each half a right angle" | `∠ e:a:c = ∟ / 2 ∧ ∠ a:e:c = ∟ / 2` |
| "AEB is a right angle" | `∠ a:e:b = ∟` |
| "side BD equals side GD" | `|(b─d)| = |(g─d)|` |
| "drawn at right-angles to AB" (construction) | `∠ ...:c:... = ∟` (the right angle it creates) |
| "made equal to AC" (construction) | `|(c─e)| = |(a─c)|` |
| "drawn parallel to AD" (construction) | `e.onLine EF ∧ ¬(EF.intersectsLine AD)` |
| "let EA and EB be joined" (construction) | `distinctPointsOnLine e a EA ∧ distinctPointsOnLine e b EB` |
| "sum of squares on AD and DB is double..." | `|(a─d)|*|(a─d)| + |(d─b)|*|(d─b)| = 2 * (...)` |

---

## Diagram usage

The diagram tells you:
- Which Euclid label ($A$, $B$, $CE$...) corresponds to which geometric object
- The vertex order of named figures (when Euclid says "rectangle BDHF", the diagram shows which
  corners are adjacent — this determines the triangulation)
- Which lines intersect to produce which points (e.g., G is where BD meets CF)

The diagram does NOT tell you claim types — only labels and spatial relationships.
