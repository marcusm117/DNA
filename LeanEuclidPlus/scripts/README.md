# `scripts/` — the faithful-pipeline tooling

The pipeline for making a Euclid proof *faithful* is **A → B → C** (see `../FAITHFUL.md` and the
`faithful-map` / `faithful-prove` skills). These scripts implement phases B and C plus the audits.

> **Run every script BARE from the repo's `LeanEuclidPlus/` dir** (e.g. `python3 scripts/check_step.py
> Book2/Prop04 5`). No `cd`, no pipes — see the project CLAUDE.md tool-hygiene rules.

## Architecture (flat by design — do not folderize)

One shared library, several thin entrypoints that import it. **New features ADD functions to
`faithful_lib.py` (or a new `<verb>.py` entrypoint that imports it) — they do NOT pile up as new
standalone scripts.** At this scale (a handful of entrypoints around one lib) a flat dir + this index
beats folders, which would only break the `import faithful_lib` adjacency and the hardcoded
`scripts/<x>.py` paths in CLAUDE.md / FAITHFUL.md / the skills.

```
faithful_lib.py   ← shared CORE (no CLI): SF/SP/P atom, flock+wall-capped builds, parsing, naming law
      ▲ imported by
  check_step.py · wire_main.py · smt_probe.py · check_faithful.py
```

## Entrypoints

| File | Phase / role | What it does |
|------|--------------|--------------|
| `check_step.py` | **B** (agent's only build tool) | Per-node verify: runs SF → SP → P, stops at first fail. `<propdir> <node>` (or `<N>` for `stepN`); `--subtree <node>` audits one node's cone; `--all` is the single final gate-B audit. Never leaves a file modified (atomic revert). |
| `wire_main.py` | **C** (human; only script that writes for keeps) | After `--all` passes: commits the wiring into `Main.lean`, strips 30s caps, builds Main once. `--unwire` reverses it back to a Phase-B state. |
| `check_faithful.py` | **C audit** | Pure-text, no Lean/SMT. Criterion 1 (exact text recovery vs `Book{N}/data/texts_proofs/`) + criterion 2. Has an `--olean` mode (authoritative, book-aware). |
| `check_steps.py` | **A/C guard** | Snapshots approved `euclid_sentence` CLAIM TYPES (`--save`) and diffs later — claims unchanged since gate A. |
| `check_signatures.py` | **C guard** | Snapshots every `theorem proposition_*` SIGNATURE and diffs — confirms no proposition statement was altered. |
| `smt_probe.py` | research / diagnostics | Builds the "should-close-but-times-out" SMT failure catalog (two-sided evidence per node). Not part of the A→B→C gate. |
| `bake_index.py` | research / tooling | PURE-PARSE fact database of EVERY declaration (axiom/def/abbrev/opaque/prop/helper/step) → `.lake/index.jsonl`. No Lean, no builds. Incremental: re-parses only changed `.lean` files. `--rebuild` for a full re-parse. You rarely run it directly — `find.py` re-bakes on every query. |
| `find.py` | research / tooling | **The sanctioned smart-grep** over `bake_index`'s DB — query declarations by `--concludes`/`--consumes`/`--mentions` (symbol×role×polarity; SYM accepts source forms like `Triangle.area`/`∟`/`Point.onLine` and ERRORS on an unknown symbol), `--book`/`--prop` (numeric location), `--cites`/`--depends-of`, `--name` glob, `--grep` (regex over **signature + docstring** — search the math), all combinable. Output is one line per match, `--show {full,conclusion,hyps}` picks which region to print (independent of the filter), `--full` disables width-truncation. Hides the 500+ noisy step files by default — `--kind step` to browse, `--steps` to widen another query. Use this instead of grepping the theory files. |

## Shell wrappers

| File | For | What |
|------|-----|------|
| `safe_build.sh <target>` | **humans only** | Serialized `lake build` under a flock (prevents `.lake` corruption from parallel builds). Agents are hard-denied raw builds and use `check_step` instead. |
| `phase_c.sh <propdir>` | Phase C runner | Chains `wire_main.py` + `check_steps.py` + `check_signatures.py`. |
| `check_faithful.sh <target>` | Phase C | Wrapper around the olean-mode faithfulness check. |

## Data (generated snapshots — checked in)

- `proposition_signatures.json` — gate for `check_signatures.py`.
- `step_signatures.json` — gate for `check_steps.py`.

(`.lake/index.jsonl` + `.lake/index.manifest.json` are `bake_index`'s output — git-ignored, NOT
checked in; rebuilt on demand.)

## Tests

`tests/` holds the parse-only sanity suite for `bake_index.py` / `find.py` / the `faithful_lib` parse
helpers — pure-parse (no Lean), runs in milliseconds: `python3 -m pytest tests/`. See `tests/README.md`.

## Adding a feature (the convention)

1. Shared logic (build/parse/SMT/dep-graph) → a function in **`faithful_lib.py`**.
2. A new user-facing tool → a new **`<verb>.py`** that does `import faithful_lib as L` and owns only its
   argparse + orchestration.
3. Keep builds going through `faithful_lib`'s flock+wall-cap path — never shell out to raw `lake`.
