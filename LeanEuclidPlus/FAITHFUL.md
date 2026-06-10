# Making proofs faithful — the order of operations (human guide)

Run everything from `LeanEuclidPlus/`. Launch Claude from the repo root `DNA/` (high effort).
Each Book-2 prop is a folder: `Book2/PropNN/Main.lean` (the proposition + `euclid_sentence`s) and
`Book2/PropNN/stepN.lean` (one proof file per sentence).

---

## ONE TIME (before any prop)
Snapshot the trusted statements, so any later change to a `theorem proposition_*` is caught:
```
python3 scripts/check_signatures.py --save
```

## PER PROP (e.g. Prop04) — the loop

**1.  Phase A (translation):**   `/faithful-map Book2/Prop04/Main.lean`

**2.  faithful-map runs, then STOPS.**  It wipes the old proof and writes the *sentence map* in
     `Main.lean`: each Euclid sentence → an `euclid_sentence` with its Lean claim type (proofs are
     `sorry`-stubbed step files). It reports the map and waits. (Pure translation — no proving.)

**3.  ▶ HUMAN: review + approve.**
   - Read each claim type — does it honestly say what that Euclid sentence says? (Only you can judge
     this. Use `Book2/data/diagrams/4.png` if helpful.)
   - When happy, freeze it:  `python3 scripts/check_steps.py --save Book2/Prop04/Main.lean`

**4.  Phase B (proving):**   `/faithful-prove Book2/Prop04/Main.lean`
     Runs end-to-end, no stops: proves each `stepN.lean`, builds the prop, runs the authoritative check.

**5.  ▶ HUMAN: sign off.**  Confirm nothing was fudged:
```
scripts/safe_build.sh Book2.Prop04.Main          # builds, zero sorry
scripts/check_faithful.sh Book2                  # text + deps PASS (book-aware)
python3 scripts/check_steps.py Book2/Prop04/Main.lean   # claims unchanged since you approved
python3 scripts/check_signatures.py              # no statement was altered
```
All PASS/OK (exit 0) → Prop04 is faithful. Done.

---

That's the whole process. Many props in parallel = one agent per folder; approve each at step 3 in
any order. Book 1 (`Book/`) is untouched. Already-done props are already in folders — agents add
`stepN.lean` files, never a scratch dir or merge step.

## The 4 scripts (reference)
- `check_signatures.py` — guards proposition **statements** (must never change). `--save` / bare-diff.
- `check_steps.py` — guards approved **claim types**. `--save Book2/PropNN/Main.lean` / bare-diff.
- `check_faithful.sh Book2` — **authoritative** faithfulness check (needs a build first).
- `check_faithful.py "Book2/PropNN/Main.lean"` — quick offline sanity (agent uses during dev).
