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
