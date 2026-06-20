# Agent notes (global)

Freeform scratchpad for cross-cutting findings: tooling bugs, nice-to-have scripts, token-savers,
quirks worth remembering. No schema — append whatever's useful. Per-prop notes go in
`Book<N>/PropNN/agent_notes.md` (created on demand by the agent working that prop; also freeform).

Both files are `.md` → invisible to every scanner (`bake_index.scan_targets`, `prop_files`,
`integrity_scan` — all glob `*.lean` only), so nothing here is ever parsed back or enforced.

## Known items
- idea-09 "cheapest next move" ranker is deferred (needs a live build + first-order matcher).
- find.py: write hypotheses as a SUM, not `2 * x` — the SMT translator chokes on `2 *` in hyp position.
