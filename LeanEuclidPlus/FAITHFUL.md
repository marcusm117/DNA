# Making a proof faithful — operator guide (for the human)

This is the short version: **what YOU do**, and which agent does what. The agent's detailed rules
live in the `faithful-euclid` skill; you don't need them. Run everything from `LeanEuclidPlus/`.

There are 3 phases. **You only act between phases** (review + one command). The agent does the rest.

---

## The loop, per proposition (e.g. Prop02)

**Start an agent** (launch Claude from the repo root `DNA/`, with high effort):
```
/faithful-euclid Book2/Prop02.lean
```

### Phase A — the agent writes the "sentence map" and STOPS
It splits Euclid's text into `euclid_sentence` steps and writes each step's Lean claim (proof = `sorry`).
It stops and shows you the map (locator → Euclid text → claim type).

**→ YOUR ACTION:**
1. **Review the claim types.** Does each Lean type honestly say what that Euclid sentence says? (This
   is the one thing no script can check — only you can.) Look at `Book2/diagrams/2.png` if unsure.
2. If good, **freeze it**:
   ```
   python3 scripts/check_steps.py --save Book2/Prop02.lean
   ```
   (Saves the approved claim types. From now on the agent can't silently weaken them.)
3. Tell the agent to continue (or start a fresh one — it auto-detects it's now in Phase B).

### Phase B — the agent proves each step in its own file (automatic)
Each sentence becomes a separate file under `Scratch/Book2/Prop02/` that builds on its own (~30s).
No action from you; it just grinds until every step builds with no `sorry`.

### Phase C — the agent reunites everything and runs the final check (automatic)
It merges the steps into `Book2/Prop02.lean` (+ `Book2/Prop02_steps.lean`), builds the whole prop,
and runs the authoritative faithfulness check.

**→ YOUR ACTION (final sign-off):** run the two guards yourself to be sure nothing was fudged:
```
python3 scripts/check_steps.py        Book2/Prop02.lean   # claim types unchanged since you approved?
python3 scripts/check_signatures.py                       # no proposition STATEMENT was altered?
scripts/check_faithful.sh Book2                           # the real faithfulness check (needs a build first)
```
All three say PASS/OK with exit 0 → the prop is faithful. Done.

---

## Running many props at once
Fully supported. One agent per prop, each owns its own files — no conflict. Approve each prop's
Phase A whenever it's ready (`check_steps.py --save Book2/PropNN.lean` merges per-prop, any order).

---

## The scripts, one line each
| Script | What it's for | Who runs it |
|---|---|---|
| `scripts/check_steps.py` | guards the approved **claim types** (Phase A output) | you: `--save` to approve, bare to verify |
| `scripts/check_signatures.py` | guards the **proposition statements** (must never change) | you, anytime |
| `scripts/check_faithful.sh Book2` | the **authoritative** faithfulness check (text + deps, book-aware) | you / agent, after a build |
| `scripts/check_faithful.py "Book2/PropNN.lean"` | quick offline sanity (no build) — text tiling + a lint | agent during dev |
| `scripts/safe_build.sh <Target>` | the only safe way to build (lock for parallel agents) | agent |

`check_faithful.py` checks two things automatically: (1) the sentences concatenate to Euclid's exact
text, (3) cited props are referenced. The third thing — **does each claim honestly capture its
sentence** — is the part only YOU check, in Phase A review.

---

## If something looks wrong
- A guard prints `CHANGED`/`FAIL` → the agent altered a frozen claim or a statement. Look at the diff
  it prints; decide if the change is justified. If yes, re-`--save`; if no, tell the agent to revert.
- You can always `git diff` — agents are not allowed to run git, so your working tree is the truth.
