# 02 — `SM` smell step (short-timeout triviality/falsity check before SF)

**Status:** idea · **Serves:** #1, #3, #4 · **Effort:** low · **Priority:** 2nd

## Problem it solves

The pipeline today is `SF → SP → P`. `SF` checks *sufficiency* ("if this claim were true, does it close
the parent"). But it NEVER checks *truth* until `P` (the full proof). So the agent can design a clean
decomposition, pass `SF` on every node, prove several, then discover a leaf is **false/unprovable** — and
unwind the whole subtree of cognition. The prerequisite question "**should this even be true?**" is asked
implicitly and only answered the expensive way (by proving it).

## Why it helps (in cost terms)

Front-loads truth to the TOP of the thinking tree. The asymmetry that makes it cheap: **a false claim
returns `SAT` FAST** (the solver finds a countermodel quickly), while a true-but-hard claim times out
slowly. So a short-timeout fire of the bare claim cleanly separates three cases the agent should treat
COMPLETELY differently — and conflating them is a top thrash source.

## Sketch — add `SM` before `SF`: `check_step --smell <node>`

Fire the bare claim (no decomposition) at a SHORT timeout (~5s). Three outcomes:

| Result | Meaning | Agent action |
|--------|---------|--------------|
| **UNSAT fast** | trivially TRUE | **Don't decompose — just close it.** (Under-used cost win: agents decompose things `euclid_finish` closes directly.) |
| **SAT fast** | FALSE (countermodel) | **STOP. Fix the claim.** Decomposing a false goal is infinite thrash. |
| **timeout** | true-but-hard | Proceed to decompose (the normal `SF→SP→P` path). |

Also: `check_step` should LABEL a `SAT` verdict in any build's output with its consequence ("SAT = the
claim is false; do NOT decompose, fix the claim") — cheap, and prevents misreading `Prover returned SAT`
under load. (This exact misread nearly happened with the no-witness lemma bug — SAT meant "false as
written," not "too big.")

## Note on the agent's pushback (recorded, it's a fair point)

"If a claim is so false that `SAT` catches it, a competent agent should already know it's false." Partly
true — so SM's value is LESS about catching a stupid agent and MORE about:
1. the **UNSAT-fast branch** ("don't bother decomposing, it's trivial") — even a smart agent over-decomposes;
2. making the truth-check **mechanical and cheap** so it's always run, not skipped under confidence.

## Open questions / risks

- **Timeout calibration:** 5s? Too short → true-but-easy claims misread as "hard"; too long → erodes the
  cheapness. Tune empirically.
- **SAT reliability:** does the System-E SMT encoding reliably produce SAT (vs. unknown) for false
  geometric claims? If it often returns `unknown` instead of `SAT`, the falsity branch weakens and we lean
  on [04 numeric realizer](04-numeric-realizer.md) instead.
- Relationship to [04]: SM (abstract SMT) is the cheap first cut; the numeric realizer is the stronger
  falsity oracle. Build SM first; only build 04 if SM's SAT proves too weak.
