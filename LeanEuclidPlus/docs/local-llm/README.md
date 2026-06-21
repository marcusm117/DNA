# Local-LLM faithful-prove — idea & design notes

**Status:** experiment, not started · **Recorded:** 2026-06-21 · **Theme:** replace the (paid, Claude-driven)
faithful-prove agent with a **free, local, unattended** model on the department GPU cluster.

> This is a SEPARATE track from [`../ideas/`](../ideas/INDEX.md). Those ideas shorten the *existing*
> Claude-driven pipeline's cognition cost. This one asks a different question: **can a free local model
> run the faithful-prove loop at all** — slowly, overnight, at zero API cost? Reference for Sonnet 4.6:
> it already does *whole propositions*. The bar here is far lower: do **something** useful (write a
> decomposition structure, or certify a single leaf) autonomously.

---

## Why (the motivation)

- **Zero marginal cost.** The cluster GPUs are free; a local model proving overnight costs nothing per node.
- **Unattended.** The verifier (`check_step.py`) is ground truth, so the loop needs no human judgement —
  pass/fail is mechanical. "Slow wall-time is fine" was the explicit constraint.
- The gamble is entirely **model capability**, not infrastructure (infra is proven — see SETUP-LOG.md).

## TL;DR decision (the sequence to follow)

1. **Measure the single-model version first.** Don't build anything fancy until you've seen *how* a
   local 27B fails on the real loop. (Build = `local_prove.py`, see "Harness" below.)
2. The failure MODE dictates the next move:
   - flails on **tool calls** (good reasoning, bad calls) → try **one-model-two-modes** (below); then
     two-model planner/executor only if that's still not enough.
   - can't reason about the **DSL** at all → local-small won't save it; go A6000 + 27B, or abandon local.
   - **certifies even one leaf** autonomously → the approach has legs; optimize from there.
3. Don't pre-build the two-model split — it's premature optimization against an unmeasured failure.

---

## Hardware reality (department SLURM cluster — hard constraints)

- Single-GPU nodes only: **RTX 4090 = 24 GB** (several, often free: `gpunode32/33/34`),
  **RTX A6000 = 49 GB** (one, usually contended).
- **You cannot pool two GPUs across nodes.** vLLM tensor-parallel needs same-node GPUs; the cluster's
  4090s are on separate machines. So per-model VRAM ceiling is **24 GB (4090)** or **49 GB (A6000)**.
- Two *different* models on two nodes IS fine — they talk over HTTP (not tensor-parallel), so an
  orchestrator can call both. Costs two GPU allocations.
- **GPU jobs default to 1 core / 1 GB RAM** — always pass `-c 8 --mem 32G` or loading crawls.
- **Storage:** home (`/h/56`, shared, ~backed-up, near-full) is for code only. Bulky model weights +
  conda env go on **`/w/100/taddmao`** (the user's working dir, 200 GB+ free). See SETUP-LOG.md.

## Model choice + how far below frontier (June 2026)

| Model | Fits 4090? | Intelligence (proxy) | Notes |
|---|---|---|---|
| **Sonnet 4.6** | — (cloud) | ~52–58, SWE-bench 79.6 | reference: does whole props |
| **Qwen3.6-27B (AWQ-INT4)** | yes, **tight** (19.2 GB wts) | ~43, SWE ~77 (harness-aided) | ~1 tier below Sonnet; the one we stood up |
| Qwen3-14B (dense INT4) | yes, roomy (~9 GB) | ~35–38 | ~1 step below 27B, ~2 tiers below Sonnet; frees VRAM → big context + CUDA graphs |
| Qwen3-Coder-30B-A3B | yes but **17 GB** | — | MoE "A3B" = 3B active but **30B in VRAM**; does NOT buy context headroom; skip for that purpose |

**Honest expectation:** a local 27B/14B will likely *prove the harness works + certify easy leaves* but
**struggle to plan a real decomposition** (e.g. Prop05 step6's 25-node figure). Agentic tool-discipline
degrades faster with size than raw knowledge — so the weakest link is driving the loop, not the Lean facts.

---

## Harness design — build your OWN thin agent, not Qwen Code

For a NARROW, unattended, safety-sensitive task, a custom harness beats an off-the-shelf CLI (Qwen Code /
OpenHands). Reason: the security model inverts.

- **Off-the-shelf** gives a general `shell` tool you then try to *restrict* (deny git/rm). Unattended =
  must run in auto-approve/YOLO → no guardrails. Fighting a powerful tool.
- **Own harness** exposes a **curated menu of function-tools**; there is no shell, so **git/rm are
  unrepresentable** — capability-based security, stronger than any allowlist. The "how do I deny git?"
  worry *dissolves*: you never write a git tool.

### The curated tool menu (the whole surface)

| Tool | Wraps | Safety |
|---|---|---|
| `find(args)` | `python3 scripts/find.py <args>` | read-only declaration search; fixed cmd prefix |
| `check_step(args)` | `python3 scripts/check_step.py <propdir> <args>` (incl. `--status`, `--context`) | the verifier; model supplies only flags |
| `read_file(path)` | file read, **path validated under `LeanEuclidPlus/`** | read-only, scoped |
| `write_step_file(node, content)` | writes **only** `<propdir>/<node>.lean` (reject other paths) | the model's ONLY mutation, path-locked |

- Command prefixes are hardcoded; the model supplies only args (can't smuggle `; git push`).
- Need `ls` or similar later? **Add a scoped tool** (`list_dir`), never a general shell. Grow by safe
  additions. For faithful-prove the 4 tools likely suffice — `check_step --status` already gives structure.
- **Tools vs skill:** a tool is a callable JSON schema (model emits `tool_call`, harness runs it); the
  "skill" is prose in the system prompt. Both are in context every turn; the *history* (calls + results)
  accumulates.

### Context budget

- fixed overhead per turn: 4 tool schemas (~500 tok) + condensed brief (~2k) + task/`--status` (~1k) ≈ **~3.5k**.
- **The real hog is the reasoning model's thinking** — "say hi" burned 2,188 tokens. Over ~8 tool turns
  that's 10–30k of accumulated `<think>`. THIS fills the window, not the tools.
- Levers: cap `max_tokens`; **thinking OFF for mechanical tool turns** (`enable_thinking: false`), ON only
  for planning; **reset + resume from `--status`** when full.
- **Condense the skill.** `SKILL.md` is ~430 lines ≈ 6–8 k tokens — loading it whole eats half a 25k
  window. Give a trimmed brief (the non-negotiable rules + "use find.py / check_step") and let it pull
  specifics via tools.

### Context-maxed → reset is SAFE here

Because all state is **external** (files + the certification manifest via `check_step --status`), the model
is stateless: on reset, re-feed `condensed brief + --status + current stepN.lean` → it **resumes**, not
restarts. Best practice: **scope one node per session** so it rarely maxes; `--status` handles cross-node resume.

---

## The planner/executor idea (pocket it; don't build first)

Observation: reasoning models *plan* well but *tool-call* poorly; instruct/coder models the reverse. So split:
a **thinking model** produces the decomposition + what-to-confirm; a **non-thinking model** mechanically
drives the tools.

**Why it's leakier than it looks:** Euclid proving is **reason ↔ lookup ↔ verify, interleaved**, not
plan-then-execute. You decompose → look up an axiom (changes the plan) → check context (reveals a missing
hyp) → re-decompose. A clean split forces **constant handoffs**, each a lossy NL serialization, and a dumb
executor can't catch a bad plan. This interleaving is *why a single agent is the natural fit*.

**Cheaper version that captures most of it — one model, two MODES (preferred v2):**
- *plan call:* thinking ON, **no tools** → decomposition + anchors to confirm.
- *execute calls:* thinking OFF, **tools ON** → run the plan mechanically.
- One GPU, one server, two prompt templates. No second model/node/network handoff.

**Two-model / two-node** version: only if one-model-two-modes still flails on tool discipline. Feasible
(two 4090s on two nodes, orchestrator calls both over HTTP) but doubles complexity; defer.

---

## Concerns, ranked (be honest)

1. **Tool-calling discipline (#1 risk).** Will it emit well-formed calls, pick the right tool, not loop?
   The whole experiment. Local models are worst here vs Claude; warning sign = the 2,188-token "hi".
2. **Overthinking → context exhaustion.** Reasoning traces fill the window before a node finishes. Tunable
   (cap tokens, thinking-off, reset) but expect to tune.
3. **Can it write valid System E at all?** The `euclid_apply` DSL is unseen by any pretrained model. The
   verifier catches garbage, but pass@N only helps if it *sometimes* emits valid Lean.
4. **Speed × attempts.** ~13 tok/s eager + long reasoning + pass@N → potentially hours/node. Fine for
   batch, caps iteration speed.
5. **Operational:** interactive `srun` drops; real runs need a stable `sbatch`. fp8+tool-calling re-serve
   may surface one more vLLM quirk. Minor.

**Genuinely low-risk:** safety (capability model), plumbing (standard function-calling), per-node context
fit (with fp8 KV), reuse of `check_step`/`find.py`, cost (free).

## Open questions

- Does the 27B (or 14B) emit usable Qwen tool-calls via vLLM `--tool-call-parser hermes` reliably?
- Does fp8 KV actually reach ~25–30k usable on the 4090 for this hybrid (GDN/mamba) model? (untested)
- Is "one-model-two-modes" enough, or is the reasoning genuinely too weak without the A6000+27B?
- Certified-rate per model over a frozen N-node eval set — the ONLY metric that matters; produce it.