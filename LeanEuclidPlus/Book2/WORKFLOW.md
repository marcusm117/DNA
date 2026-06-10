# Book 2 — extension workflow

> **⚠ HISTORICAL / SUPERSEDED for the faithfulness workflow.** This doc describes the original
> hand-built setup (how Book 2's texts/diagrams/statements were created). For **making proofs
> faithful**, use [`../FAITHFUL.md`](../FAITHFUL.md) (the human operator guide) + the `faithful-euclid`
> skill — NOT the annotation approach sketched here. The dataset-extraction parts below are still
> accurate; the per-prop annotation guidance is outdated.

How to extend the LeanEuclid benchmark to Book 2 of Euclid's *Elements*, mirroring how
Book 1 (`../Book/`) was built. Book 2 ("Fundamentals of Geometric Algebra") has **14
propositions** plus 2 definitions.

## What's automated vs. manual

The text and diagrams are derived deterministically from the rfitzp LaTeX edition
(cloned at `/u/taddmao/code/autoform/Elements/Book02/`) by
[../AutoFormalization/statement/extract_book.py](../AutoFormalization/statement/extract_book.py).
It has already been run:

```bash
cd ../AutoFormalization/statement
python3 extract_book.py --book 2
```

This produced (re-runnable / idempotent) — now under `Book2/data/` (the generated corpus was moved
into a `data/` subfolder so the per-prop `PropNN/` folders aren't cluttered; `extract_book.py` writes
there for Book 2+):

- `data/texts_proofs/1.txt … 14.txt` — the **full** English statement + proof + conclusion for
  each proposition, with `$...$` math and `[Prop.~1.11]` / `[Post.~3]` / `[Def.~1.15]`
  citations kept verbatim. Greek, figures, headings, and footnotes are stripped.
- `data/diagrams/1.png … 14.png` — the English-side figure (`figNNe.eps`) rasterized to PNG,
  matching Book 1's style (~120 DPI, white bg, trimmed).

Everything below is **manual, per proposition** — this is exactly the part of Book 1 that
was done by hand. To get started you only need the proof text (already generated); add the
rest one proposition at a time.

## Per-proposition steps

Do these for each proposition N = 1 … 14.

### 1. Lean ground truth — `Book2/PropNN.lean`

`Prop01.lean … Prop14.lean` already exist as **stubs** with the correct boilerplate
(`import SystemE`, `namespace Elements.Book2`, `end Elements.Book2`, and a TODO skeleton) —
fill in the theorem(s). The `lean_lib Book2` target is already declared in `../lakefile.lean`.

Formalize the theorem (and its proof) in System E, following the conventions in
`../Book/PropNN.lean`. Template (see [../Book/Prop02.lean](../Book/Prop02.lean)):

```lean
import SystemE
-- import any earlier props you depend on, e.g.:
-- import Book.Prop47          -- a Book 1 result
-- import Book2.Prop04         -- an earlier Book 2 result

namespace Elements.Book2

theorem proposition_N : ∀ (…) , (hypotheses) → (conclusion) := by
  euclid_intros
  euclid_apply …
  use …
  euclid_finish

end Elements.Book2
```

Notes specific to Book 2:
- The namespace is `Elements.Book2` (Book 1 uses `Elements.Book1`). Cross-book references
  in proofs are e.g. `Elements.Book1.proposition_47 …`.
- Book 2 is about **rectangles, squares, and gnomons (areas)**. Before formalizing, confirm
  System E (`../SystemE/`) can express "the rectangle contained by $A$ and $BC$" and area
  equalities cleanly. If a primitive/lemma is missing, add it under `../SystemE/` — this is
  the most likely place to get stuck (Book 1 was construction/congruence-heavy; Book 2 is
  area-heavy).
- Add diagrammatic-case variants (`proposition_N'`, `proposition_N''`) when Euclid leaves a
  configuration implicit, as Book 1 does.
- Heavy area proofs may need `set_option maxHeartbeats 0 in` (cf. Book 1's Prop47).

### 1b. Faithfulness annotations + checking

Spec: [faithful.txt](faithful.txt). A proof is proof-faithful iff two criteria hold (statement
faithfulness is separate and human-checked; compiling is separate — that's `lake build`).

**Criterion 1 — text map.** Concatenating the step texts in order reproduces `texts_proofs/N.txt`
character-for-character.

**Criterion 3 — dependencies.** Every `[Prop.~B.M]` Euclid cites is referenced by an `euclid_apply`
of that prop in the same step's block (reference, not proof-of-use).

#### Annotate the proof

Three tactics (defined in [../SystemE/Meta/Tactics/Faithful.lean](../SystemE/Meta/Tactics/Faithful.lean)):

- `euclid_intro_sentence "<loc>" "<text>"` — structural; the enunciation + `Let …` + `I say that …`.
  Place after `euclid_intros`. Emits no `have`.
- `euclid_sentence "<loc>" "<text>" (name : type) := by tac` — a logical step. Identical to
  `have name : type := by tac`.
- `euclid_conclude_sentence "<loc>" "<text>"` — structural; the closing `Thus, …` + QED. Place after
  the final `exact`. Emits no `have`.

```lean
  euclid_intros
  euclid_intro_sentence "2.N.0" "If there are two straight-lines … by $A$ and $EC$."

  euclid_apply (proposition_11'' b c BC) as f                      -- cited [Prop.~1.11], in this block
  euclid_sentence "2.N.1"
    "For let $BF$ be drawn from point $B$, at right-angles to $BC$ [Prop.~1.11],"
    (step1 : ¬(f.onLine BC) ∧ ∠ f:b:c = ∟) := by euclid_finish

  exact stepK
  euclid_conclude_sentence "2.N.M" "Thus, if there are two straight-lines … required to show."
```

#### Rules

1. Locator = `"<book>.<prop>.<sentence>"`. Sentences number `0,1,2,…` contiguously; `*.0` = intro,
   last = conclusion.
2. Each annotation text is a verbatim slice of `texts_proofs/N.txt` — no edits, no stray edge spaces.
   Slices tile the whole file, joined by single spaces.
3. A cited `[Prop.~B.M]` needs its `euclid_apply (proposition_M …)` in that sentence's block (lines
   from the previous annotation to this one). Any primes (`_M`, `_M'`, `_M''`) match; book + number
   is what's checked.

Worked example: [Prop01.lean](Prop01.lean).

#### Check

| Command | Build? | Criterion 1 | Criterion 3 |
|---|---|---|---|
| `python3 scripts/check_faithful.py "Book2/PropNN.lean"` | no | exact | number-only (sanity) |
| `scripts/check_faithful.sh Book2` | needs built `.olean` | exact | book-aware (final) |

```bash
# sanity, instant, no build:
python3 scripts/check_faithful.py "Book2/Prop01.lean"

# final, book-aware:
lake build Book2                 # incremental
scripts/check_faithful.sh Book2  # = lake exe faithful_export Book2 | check_faithful.py --olean
```

The `.sh` accepts any module (one prop, `Book2`, or an aggregate importing several books — the
`.olean` folds in all transitive imports, so one call checks them all). Book-aware means
`[Prop.~1.34]` resolves to `Elements.Book1.proposition_34'` at compile time and cannot be satisfied
by a Book 2 prop of the same number.

### 2. Statement-only text — `Book2/texts/N.txt`

Create the `texts/` folder and, for each prop, copy `texts_proofs/N.txt`, then **cut out the
proof body** and replace it with a literal ` <prf> ` marker. Keep:

> (the statement) + (the setup "Let …") + (the "I say that …" claim) ` <prf> ` (the final
> "Thus, …" conclusion sentence(s))

This split is a human judgment call — that's why it's manual. Example from Book 1
([../Book/texts/2.txt](../Book/texts/2.txt)):

```
To place a straight-line equal to a given straight-line at a given point (as an extremity). Let $A$ be the given point, and $BC$ the given straight-line.  <prf>  Thus, $AL$ is also equal to $BC$. Thus, the straight-line $AL$, equal to the given straight-line $BC$, has been placed at the given point $A$.
```

The diagrams (`diagrams/N.png`) are shared by both the statement and proof views — no
separate step.

### 3. Importer — `Book2.lean`

`../Book2.lean` already exists (sibling of `../Book.lean`) with every import **commented
out**. Uncomment each `import Book2.PropNN` once that proposition compiles, mirroring
[../Book.lean](../Book.lean).

### 4. (Optional) Pipeline dataset — `book2_propositions.json`

If you want to run the autoformalization pipeline over Book 2, create
`../AutoFormalization/statement/book2_propositions.json` mirroring the existing
`book_propositions.json` (formal System E statements keyed by proposition number), and point
the pipeline's `--dataset`/`--root_dir`/`--category` at the Book 2 layout (`texts/` +
`diagrams/`).

## Re-running / Books 3 & 4

`extract_book.py` is book-parameterized. Books 3 (37 props) and 4 (16 props) share the
identical LaTeX structure, so once their target folders exist:

```bash
python3 extract_book.py --book 3
python3 extract_book.py --book 4
```

(Expected counts are asserted in the script: Book 2 = 14, Book 3 = 37, Book 4 = 16.)
