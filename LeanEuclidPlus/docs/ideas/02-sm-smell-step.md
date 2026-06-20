# 02 — `SM` smell step (short-timeout "don't over-decompose" check before SF)

**Status:** idea · **Serves:** #1, #3 · **Effort:** low · **Priority:** Program 3 (cleanup), opportunistic

> **Scope correction (operator's call, recorded — read this first).** The HEADLINE value of `SM` is the
> **UNSAT-fast branch: "don't decompose — `euclid_finish` closes this directly."** Even a competent agent
> over-decomposes — splits a goal the solver would have closed in a few seconds — and that wasted
> sub-tree of cognition is a real, frequent cost leak. THIS is what `SM` is for.
>
> The **falsity-oracle framing is explicitly DOWNWEIGHTED** (was the original headline): "fire the bare
> claim, `SAT` ⟹ it's false ⟹ stop." A smart agent must reason out *in NL* why a claim is true BEFORE it
> ever decomposes — it must NOT lean on a `SAT`/timeout code-smell as its truth signal. If the smell
> catches a falsity the agent didn't already know was false, the agent was too careless, not well-served.
> So `SM` is a guard against **over-decomposition**, not a substitute for the agent reasoning about truth.
> (The mechanical-falsity oracle, if ever wanted, is [04](04-numeric-realizer.md) — a sound disproof, kept
> separate and also downweighted for the same reason.)

## Problem it solves

The pipeline today is `SF → SP → P`. `SF` checks *sufficiency* ("if this claim were true, does it close
the parent"). It never asks whether the goal is **already trivially closable** — so the agent decomposes
goals that `euclid_finish` would have discharged directly, investing a whole sub-tree of cognition in a
split that was never needed.

## Why it helps (in cost terms)

Front-loads the "is this already trivial?" question to the TOP of the thinking tree. The asymmetry that
makes it cheap: a trivially-true claim returns **UNSAT fast**; a true-but-hard claim times out slowly. So a
short-timeout fire of the bare claim cleanly separates "just close it" from "genuinely needs decomposing."

## Sketch — add `SM` before `SF`: `check_step --smell <node>`

Fire the bare claim (no decomposition) at a SHORT timeout (~5s). Three outcomes:

| Result | Meaning | Agent action |
|--------|---------|--------------|
| **UNSAT fast** | trivially TRUE | **Don't decompose — just close it.** ← THE HEADLINE WIN. Under-used: agents decompose things `euclid_finish` closes directly. |
| **SAT fast** | FALSE (countermodel) | Downweighted (see scope correction): a smart agent should already know it's false from NL reasoning. Treat as a sanity backstop, not the reason to build `SM`. |
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
