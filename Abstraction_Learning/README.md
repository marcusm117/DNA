# Abstraction Learning

This module provides functionality to extend Domain-Specific Languages (DSL) for formal mathematics by extracting concepts from mathematical statements and formalizing them.

## Dependencies

### LeanEuclidPlus Dataset
- **Lean version**: `leanprover/lean4:v4.8.0-rc2`

### ProofNet-Hard Dataset
- **Lean version**: `leanprover/lean4:v4.7.0-rc2`
- **Mathlib commit**: `59fdb6b04d7d16825a54483d550d9572ff473abf`


## Switching Lean Versions

Use `elan` to switch between the required Lean versions:

```bash
# Switch to LeanEuclidPlus version
elan override set leanprover/lean4:v4.8.0-rc2

# Switch to ProofNet-Hard version
elan override set leanprover/lean4:v4.7.0-rc2

# Check current version
lean --version
```


## Usage

To run the 6-step DSL Extension Pipeline end-to-end, execute `extend_dsl.py` with the desired dataset:

```bash
# For LeanEuclidPlus dataset
python extend_dsl.py --dataset LeanEuclidPlus

# For ProofNet-Hard dataset
python extend_dsl.py --dataset ProofNet-Lean4_proof_hard
```
