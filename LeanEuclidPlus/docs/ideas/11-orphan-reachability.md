# 11 — Orphan / reachability check (find nodes & files not connected to the top-level file)

**Status:** idea · **Serves:** #3 (test + pinpoint), #4 (did I break / leave something?) · **Effort:** low
· **Priority:** **Program 2 — the QUICK WIN.** Do it early/whenever: ~15 lines reusing existing machinery,
independent of everything, and the cheapest fix for the exact failure that motivated
[10](10-contract-deps-incremental-certs.md) (dead leftover files silently pass `--check`, then blow up `--all`).

## The bug that triggered this

On Prop05, `check_step --subtree step7` PASSED but `--all` FAILED, deep under `step7_dfpar_boffDG`. The
deepest failure was a real zero-SMT `assumption` failure in a node whose claim was a bare **line equality**
(`AB = DG` — `euclid_apply` `subst`s it, leaving `AB = AB`, which the structural closer can't discharge).

But the node was never supposed to be audited at all: `step7_dfpar_boffDG.lean`,
`step7_dfpar_boffDG_abdg.lean`, `step7_dfpar_boffDG_dgcene.lean`, and `step7_dfpar_rest.lean` were
**dead leftovers** from a superseded decomposition. The live `step7_dfpar` cone routes through the
granular `_dgbf/_boff/_goff/_doff/_ss/_abef/_body` sub-nodes; nothing — no `have`, no import — references
the `boffDG`/`rest` files anywhere in the repo. They were orphans.

**Why each existing tool missed it:**
- `--subtree step7_dfpar` walks **Cone(step7_dfpar)** = nodes physically reachable through `step7_dfpar`'s
  `have`s. The orphans aren't in that cone, so `--subtree` correctly ignores them — and passes.
- `--all` globs **every `.lean` file on disk** (`prop_files` → `parse_occurrences`) and audits every node
  in every file, **reachable or not**. So it tripped over the orphan's broken node and failed — with no
  hint that the node was dead rather than a genuine prerequisite.
- `--check`'s `integrity_scan` checks naming law / caps / no-stray-sorry per file, but has **no notion of
  reachability** — an orphan file that is internally well-formed passes `--check` silently.

**This is a recurring hazard, not a one-off:** every time a decomposition is superseded (you split a fat
node a new way, or rename a sub-node), the OLD backing files become orphans. They keep building in
isolation, keep passing `--check`, and silently wait to blow up the final `--all` (or worse, get wired by
a stale reference). Nothing currently flags them.

## Why [10] does NOT cover this (they're complementary, not the same)

[10] (`@deps` + contract certs) records and audits the **edges between LIVE nodes** ("step7 consumes
step7_dfpar's claim"). An orphan has **no inbound edge from anything live** — so [10]'s named wire never
*mentions* it, and therefore can't flag it; it just silently doesn't audit it. And `--all` still globs the
file off disk regardless of [10]. So even with [10] fully built, the orphan's broken node still sits there
and `--all` still trips over it. The missing primitive is a **reachability pass from a root set** that
reports what is NOT reached. Orthogonal to [10]; cheap; do it first.

## The idea, in one line

Build the containment graph (already exists), pick a **root set**, walk down, and report every node/file
**not reached from the roots** = dead → delete (or investigate).

## Two failure shapes it must catch (both, via ONE reachability walk)

1. **Connected to nothing** — no live node references this file's node at all (pure orphan; the
   `boffDG`/`rest` parents).
2. **Used, but not connected to the top-level file** — node A is referenced only by node B, but B itself is
   unreachable from Main. A is "used" locally yet dead globally (the nested `_abdg`/`_dgcene`, referenced
   only by the already-dead `boffDG`).

A naive "is this name referenced by any `have` anywhere?" check catches (1) but **misses (2)** — the nested
orphans look "used." A reachability walk from the roots catches both, because a node counts as LIVE only if
there is a *path from a root*, not merely an inbound edge. This is ordinary mark-and-sweep garbage
collection over the containment DAG.

## Scope knob — which roots (the "this tree / this prop / all props" choice)

| Scope | Root set | Catches |
|-------|----------|---------|
| **whole-prop** (default) | Main's `euclid_sentence` nodes + Main-level `have`s | dead files in this prop (the boffDG case) |
| **subtree X** | `{X}` | files that *look* like X's cone (e.g. share the `step7_dfpar_` name prefix) but aren't actually wired into it |
| **all-props** | every prop's Main | a whole `PropNN/` folder nobody builds |

The name PREFIX (`step7_dfpar_…`) is a mnemonic, NOT containment — that's exactly the trap. Reachability is
defined by graph edges (a `have <name>` referencing a node), never by name similarity.

## Sketch (reuses existing machinery — no new parsing)

Everything needed is already in `faithful_lib.py`:
- `parse_occurrences(propdir)` → every node NAME across every file on disk (the universe).
- `_containment(propdir)` → `children[name]` = the sub-node names inside `name`'s backing file (the edges).
- The roots = nodes whose container file is `Main.lean` (the `kind == "sentence"` nodes + Main-level
  `have`s). `_bottom_up(occs, children, roots)` already does the reachable walk and returns reachable names.

So the check is essentially:
```
reachable = set(_bottom_up(occs, children, roots))     # mark
universe  = set(occs.keys())                            # every node on disk
orphans   = universe - reachable                        # sweep
# map orphan node-names → their backing files; report file + "not reachable from <roots>"
```
Plus: a backing FILE whose theorem defines a node-name that is an orphan (and no live node shares that
file) is a dead FILE → safe to delete.

### Surface
- Fold into `--check` as a **warning** (not a hard fail by default — a freshly-written-but-not-yet-wired
  file is a transient orphan during normal Phase-B work, so don't abort on it): `--check` prints
  `WARN: N orphan node(s) not reachable from Main: step7_dfpar_boffDG (step7_dfpar_boffDG.lean), …`.
- Optional dedicated mode `check_step <propdir> --orphans [--scope subtree X | --all-props]` for an explicit
  report + the delete-candidate file list.
- `--all` could optionally **refuse to audit orphans** (or audit them but label them `ORPHAN — dead, not in
  any cone; delete or wire`) so a dead node never again presents as a mysterious deep `--all` failure.

## Open questions / risks

- **Transient orphans during Phase B are normal.** When you `Write` a new `stepN_sub.lean` before adding its
  `have stepN_sub` to the parent, it's briefly an orphan. → WARN, never hard-fail in `--check`; only the
  explicit `--orphans` mode (or a `--strict`) treats it as an error. The agent reads the warning and either
  wires it or deletes it.
- **Shared helpers are fine** — a helper reached from ANY live root is live; mark-and-sweep handles fan-in
  for free (it's reachable, full stop).
- **Don't auto-delete.** Report delete-candidates; a human/agent confirms (a file could be an
  intentionally-staged not-yet-wired helper). The reachability verdict is mechanical; the delete decision
  isn't.
- **`--all-props` cost:** parse-only over the whole tree, sub-second (no builds) — same as `bake_index`
  in [01]. Cheap.

## Relationship to other ideas

- **Complements [10]:** [10] audits edges between live nodes + invalidation on contract change; THIS finds
  nodes with no live edge at all. [10] makes the live graph trustworthy; [11] keeps the file tree free of
  dead weight that `--all` would otherwise trip on. Build [11] first (low effort, immediate).
- **Falls out of [01]'s parse infra** if that's built (same `parse_occurrences`/containment walk), but needs
  none of [01] — it's implementable today against `faithful_lib.py` alone.
