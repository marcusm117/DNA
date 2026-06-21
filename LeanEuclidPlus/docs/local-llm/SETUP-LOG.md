# vLLM-on-cluster setup log (so we never re-debug this)

**Recorded:** 2026-06-21 · companion to [README.md](README.md). The first stand-up of Qwen3.6-27B on a
4090 took ~2 hours of debugging; this captures the working recipe so the next time is ~10 minutes.

## The working stack

- **Node:** any idle RTX_4090 (`gpunode32/33/34`). Driver supports **CUDA 12.9 max** (`12090`).
- **Model:** `cyankiwi/Qwen3.6-27B-AWQ-INT4` — note it's packaged as **`compressed-tensors`**, NOT awq,
  despite the name (so DON'T pass `--quantization awq`; let vLLM auto-detect).
- **vLLM:** `0.23.0`, but the **CUDA-12.9 build** (the PyPI default is CUDA-13 and will NOT run here).

## Storage (do this first — home is full + shared)

```bash
# everything bulky on /w, nothing on /h/56 (home):
export HF_HOME=/w/100/taddmao/hf
export PIP_CACHE_DIR=/w/100/taddmao/pip-cache
export CONDA_PKGS_DIRS=/w/100/taddmao/conda-pkgs
```
- `/h/56` (home) = shared, ~backed-up, near-full → **code only**.
- `/w/100/taddmao` = working dir, 200 GB+ free, not backed up → **env + weights + caches**.
- node-local `/tmp` is big but per-node and wiped — don't put the model there (re-downloads each job).

## Install (the gotchas that cost the 2 hours)

1. Fresh env (vLLM drags a heavy torch/CUDA stack — don't pollute `base`):
   ```bash
   conda create -n vllm python=3.12 -y && conda activate vllm
   pip install vllm "huggingface_hub[cli]"
   ```
2. **CRITICAL — the CUDA mismatch.** Plain `pip install vllm` pulls a **CUDA-13** torch + a CUDA-13
   `vllm._C`; the 4090 driver maxes at 12.9 → `RuntimeError: NVIDIA driver too old (found 12090)` then
   `ImportError: libcudart.so.13`. `--torch-backend=cu129` fixes torch but NOT vllm's own `_C`. The real
   fix is to install the **cu129-compiled vLLM wheel** from GitHub releases (NOT PyPI):
   ```bash
   pip install --force-reinstall --no-deps \
     "https://github.com/vllm-project/vllm/releases/download/v0.23.0/vllm-0.23.0+cu129-cp38-abi3-manylinux_2_28_x86_64.whl"
   ```
   `--no-deps` so it doesn't clobber torch; `--force-reinstall` to replace the cu13 vllm. Verify on a GPU
   node: `python -c "import torch,vllm; print(torch.version.cuda, torch.cuda.is_available())"` → `12.9 True`.
   (Bake this wheel into the sbatch — **never** plain `pip install vllm`, it reverts to cu13.)

## Serve

Get a node + serve (re-export the storage vars on the node; they don't always follow `srun`):
```bash
srun -p gpunodes --constraint=RTX_4090 --gres=gpu:1 -c 8 --mem=32G --pty bash
conda activate vllm
export HF_HOME=/w/100/taddmao/hf
vllm serve cyankiwi/Qwen3.6-27B-AWQ-INT4 \
  --reasoning-parser qwen3 \
  --max-model-len 12288 \
  --gpu-memory-utilization 0.95 \
  --enforce-eager \
  --port 8000
```

### Why each flag (memory is the binding constraint on 24 GB)

- **(no `--quantization`)** — model is `compressed-tensors`; passing `awq` errors on a config mismatch.
- **`--enforce-eager`** — 27B weights (19.2 GB) leave no room for CUDA-graph capture → OOM. Eager skips
  graph capture + torch.compile, freeing ~3 GB and skipping the ~86 s compile. Cost: ~13 tok/s (slower
  generation, identical outputs). Right trade for a correctness experiment.
- **`--max-model-len 12288`** — after weights, only ~1.15 GB KV cache fits; vLLM computed max len ≈ 15680,
  so 12288 is safely under. (16384 errors: "needs more KV than available.")
- **`--gpu-memory-utilization 0.95`** — we own the whole GPU; can push 0.97.

Ready signal: `INFO ... Uvicorn running on http://0.0.0.0:8000`. First load downloads ~16 GB → `/w` (one-time).

### Proposed upgrade for the agentic loop (UNTESTED as of 2026-06-21)

To roughly double context + enable tool-calling:
```bash
vllm serve cyankiwi/Qwen3.6-27B-AWQ-INT4 \
  --reasoning-parser qwen3 \
  --kv-cache-dtype fp8 \            # ~halves per-token KV → ~25-30k context
  --max-model-len 24576 \          # raise once fp8 frees KV (tune to what fits)
  --gpu-memory-utilization 0.97 \
  --enforce-eager \
  --enable-auto-tool-choice \      # OpenAI tools API
  --tool-call-parser hermes \      # Qwen tool-call format
  --port 8000
```
Verify the fp8 KV math actually reaches the target context before trusting it (this model is a hybrid
GDN/mamba arch — KV accounting differs from plain attention).

## Smoke test + behavior note

```bash
# second shell on the SAME node (don't grab a 2nd GPU):
srun --jobid=<JOBID> --overlap --pty bash
curl http://localhost:8000/v1/chat/completions -H "Content-Type: application/json" \
  -d '{"model":"cyankiwi/Qwen3.6-27B-AWQ-INT4","messages":[{"role":"user","content":"say hi in 5 words"}]}'
```

**Observed (the warning sign):** correct answer, but **2,188 completion tokens** to say "hi" — it looped,
re-counting the same phrase ~30×. This is reasoning-model *overthinking*, likely worsened by INT4. It's
the empirical basis for concern #1/#2 in the README: cap reasoning + thinking-off for mechanical turns.

## Operational

- Interactive `srun --pty` keeps dropping you back to the login node; for real runs use a stable **`sbatch`**
  so the server survives. Put the storage exports + the cu129-wheel install + the serve command in it.
- The first cold start is ~5 min (load + compile/warmup); eager + cached compile makes restarts faster.