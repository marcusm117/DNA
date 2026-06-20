# 05 — Timeout diagnostics (which line / what context on a wall-kill)

**Status:** idea · **Serves:** #3 · **Effort:** low (spike first) · **Priority:** 4th

## Problem it solves

When a build hits the 30s wall and gets SIGKILL'd, `check_step` reports "timed out" but NOT *where* — which
`have`/tactic was running, or what made it slow. The agent then re-thinks blind.

## The honest constraints

- At a PROPERLY-DECOMPOSED leaf, you already know the line — it IS the leaf. The "which line is slow"
  problem only exists for a FAT multi-`have` `euclid_finish`, which the methodology already says to
  decompose. So the high-value case is partly one you're told to avoid.
- For a single `euclid_finish` that times out, there is NO "line 73 was slow" inside the solver call — the
  solver simply never returned; the whole translated query is the slow thing. We can't get a sub-call line
  number for free.

## What we CAN do (two tiers)

**Tier 1 — cheap, do alongside other work.** On a wall-kill, `check_step` already has the dev-state source;
print the **goal** and the **context size (hyp count)** of the node that was building, plus the standard
advice ("bloat is the usual cause → slim the signature or decompose"). Context bloat is the #1 timeout
cause, so hyp-count is a real signal.

**Tier 2 — last-profiler-line SPIKE (30 min, then decide).** Run the build with `set_option profiler true`
(or `trace.profiler`), which streams per-elaboration timings to stdout as it goes. `check_step` already
line-buffers stdout, so on SIGKILL capture the **last profiler line emitted** → the tactic/`have` that was
running at the wall. Cheap IF it works.
- **The uncertainty (why it's a spike, not a commitment):** not sure Lean FLUSHES profiler lines mid-block
  before the kill — it may buffer to end-of-declaration, in which case we get nothing. Test on one fat
  timeout; if lines stream, add it to the timeout message; if not, drop it and keep Tier 1.

**Tier 3 — `--bisect` (later, maybe).** Re-run the goal with half the hypotheses removed, recurse to find
which single hyp explodes the search; report "hyp `hX` is what makes this blow up." This is several builds
automated behind one command — VIABLE precisely because builds are free (cost model). Only worth it if
timeouts remain a frequent thrash source after Tier 1/2.

## Open questions / risks

- Does `trace.profiler` output survive a SIGKILL with line-buffering? (the spike answers this.)
- `--bisect` assumes one dominant culprit hyp; multiple-interacting-hyps blow-ups won't bisect cleanly.

## Addendum — SP failure message: print ONLY the unmet hypotheses, suppress the context dump (do this first)

**Status:** idea · **Serves:** #3 · **Effort:** very low · separate from the timeout tiers above (this is
about the SP/`assumption` failure path, not a wall-kill).

**The observation (from the Prop05 `step7_dhg` repair).** When SP fails, the wire's
`euclid_apply (helper … (by assumption) (by assumption) …)` is ONE line; each `(by assumption)` that can't
find its binder emits a full Lean `tactic 'assumption' failed` error — **including the entire ~80-line local
context** — ending in the goal it couldn't discharge (`⊢ ¬KM.intersectsLine EF`). With 6 absent hyps that's
6 × ~80 = ~480 lines, the SAME context repeated, to convey 6 facts.

**The whole signal is those 6 `⊢` goals.** They ARE the absent hypotheses — that's exactly how the repair
was diagnosed ("these 6 aren't at the call site → drop from signature, derive in-body"). The context dump
underneath each one is pure noise here, because SP's ONLY question is "is this fact present or not," and the
answer is just the list of facts that weren't.

**The fix.** On an SP `assumption` failure, parse Lean's errors, strip the context, and print only the
unmet binders:
```
SP FAIL step7_dhg — these 6 hypotheses are not present at the call site:
  ¬KM.intersectsLine EF
  ¬e.onLine DG
  ¬b.onLine DG
  ¬d.onLine KM
  ¬b.onLine KM
  ¬g.onLine KM
→ remove each from the helper signature and derive it in-body, OR supply it at the call site.
```
No context block, no dedup, no diff, no present/absent table — just the list. (Earlier framings of this —
"de-dup the repeated context," "present/absent binder table" — were over-engineered: they tried to PRESERVE
a context dump that, for SP, should not be shown at all.)

**Scope it to SP, not everywhere.** This applies to the SP `(by assumption)` failure ONLY. A **P** failure
(a real `euclid_finish`/`euclid_assert` inside a body) is a different animal — there the goal+context can
genuinely matter, so don't strip it. Rule: "on an SP `assumption` failure, suppress context, list only the
unmet binders."

**Cost honesty:** cheap and high-frequency-path (every SP failure, forever), BUT in the run that motivated
it the SP diagnosis was already the *fast* part — the expensive parts were the `--subtree`-vs-`--all`
confusion and proving the orphans dead ([11](11-orphan-reachability.md)). So this is genuine low-effort
polish, ranked below 11 and 10's diagnostic — not a headline win.

**Risk:** it's a parse-and-reformat of Lean's raw error stream (not literally free); must reliably pick out
each `tactic 'assumption' failed` block's goal line and drop its context, across however Lean formats them.

### Considered and DEFERRED (don't relitigate): line-level / `--after <have>` context

A `check_step --context <node> --after <have-name>` that prints the context *partway down a leaf body*
(signature + the preceding `have`s' outputs) was considered. **Deferred:** it overlaps with the methodology's
own move — when a mid-body step is hard, you DECOMPOSE it into its own sub-node, and then plain
`--context <subnode>` answers at the right granularity again. So line-level context is only useful for
*exploration before deciding to decompose* — a narrow window — and didn't save the `step7_dhg` repair (whose
body already built; the problem was the signature, which is pure node-entry context). Building it risks
encouraging fat-leaf spelunking over decomposition. Node-entry `--context <node>` is enough for the
suppliability/wire questions, which are the common, high-value case.
