# Prop05 Manual Workflow Guide

**Current Status:** Prop05 is in **Phase B** (faithful-prove). You're working on proving the steps manually.

## Quick Reference - What to Run

**IMPORTANT:** All `scripts/check_step.py` commands must be run from the `LeanEuclidPlus/` directory:
```bash
cd /u/taddmao/code/autoform/DNA/LeanEuclidPlus
```

### 1. Check Overall Status (Where Are We?)

```bash
# From LeanEuclidPlus/ - Structural integrity + what's done
python3 scripts/check_step.py Book2/Prop05 --check

# What changed since last certification
python3 scripts/check_step.py Book2/Prop05 --whatchanged
```

### 2. Working on a Specific Step

**Before editing** - see what hypotheses are available:
```bash
python3 scripts/check_step.py Book2/Prop05 --context step11
```

**After writing the proof** - check just that node (SF→SP→P):
```bash
python3 scripts/check_step.py Book2/Prop05 step11
# Or use a sub-node name like:
python3 scripts/check_step.py Book2/Prop05 step11_ahpar
```

**Check if a container and all its sub-nodes are done:**
```bash
python3 scripts/check_step.py Book2/Prop05 --subtree step11
```

### 3. Check Individual Aspects (Diagnostic)

```bash
# Just check if the claim type is well-formed (SF - Sufficient)
python3 scripts/check_step.py Book2/Prop05 --sufficient step11

# Just check if parent can supply the hypotheses (SP - Suppliable)
python3 scripts/check_step.py Book2/Prop05 --suppliable step11

# Just check if it builds zero-sorry (P - Provable, for leaves only)
python3 scripts/check_step.py Book2/Prop05 --provable step11
```

### 4. Final Checks (After All Steps Done)

```bash
# The BIG ONE - checks everything bottom-up (run ONCE at the end)
python3 scripts/check_step.py Book2/Prop05 --all

# If --all passes, proceed to Phase C:
python3 scripts/phase_c.sh Book2/Prop05
```

## Current Prop05 Status (June 16, 2026)

**Certified:** 35 nodes including:
- ✅ step1 through step6 (and all 30+ step6 sub-nodes)
- ✅ step9, step10, step14, step16, step18
- ✅ Most of step11 sub-nodes (step11_ahpar and its children)

**Missing backing files (need to create & prove):**
1. `step11_ahpar_abkm.lean` - prove AB ∥ KM (should be trivial, just intersection_symm)
2. `step7.lean` - CM = DF (gnomon arithmetic)
3. `step8.lean` - CM = AL via AC = CB (uses prop_36)
4. `step12.lean` - AH = |(a─d)| * |(d─b)| (rectangle area)
5. `step13.lean` - |(d─h)| = |(d─b)| (parallel line property)
6. `step15.lean` - LG = |(c─d)| * |(c─d)| (square area)
7. `step17.lean` - gnomon + LG = whole square CEFB

**Priority order:**
1. **step11_ahpar_abkm** (easiest - just one line, symmetry)
2. **step7, step8, step9** (gnomon equalities - step9 is done, pattern for 7-8)
3. **step12, step13** (rectangle/parallelogram properties)
4. **step15, step17** (final square arithmetic)

## File Structure

```
Book2/Prop05/
├── Main.lean           # All step bodies are `:= by sorry`
├── step1.lean          # Proven
├── step2.lean          # Proven
├── ...
├── step6.lean          # Container with many sub-nodes
│   ├── step6_big.lean
│   ├── step6_bmf.lean
│   ├── step6_par1.lean
│   └── ... (30+ sub-files)
├── step7.lean          # ← Need to work on
├── step8.lean          # ← Need to work on
├── step11.lean         # Container, proven
│   ├── step11_ahpar.lean
│   └── ... (15+ sub-files)
└── ... (remaining steps)
```

## Tips for Manual Proving

1. **Start simple:** Work on leaves first (steps with no sub-nodes)
2. **Use `--context`** to see what's available before writing the proof
3. **After each file edit:** Run `--whatchanged` to see minimal recheck set
4. **Don't raise caps:** If a proof times out (>30s), decompose into more `have` sub-nodes
5. **Check incrementally:** Use `check_step.py Book2/Prop05 <node>` after each proof
6. **Use `--subtree`** when a container and its leaves are done
7. **Only run `--all` ONCE** at the very end when everything is done

## Common Patterns

**To add a decomposition** (when a step is too hard):
1. Create `step7_helper.lean` with a sub-claim
2. In `step7.lean`, add: `have step7_helper : <claim> := by sorry`
3. Prove `step7_helper.lean` in isolation
4. Use it in `step7.lean`'s main proof

**The 30-second rule:**
- Every build must complete in ≤30s
- If it doesn't → decompose into smaller `have` sub-nodes
- Never raise the timeout cap

## Where to Look Next

Based on Main.lean, **immediate next steps to work on:**
- **step7:** CM = DF (area equality, should be straightforward arithmetic)
- **step8:** CM = AL via AC = CB (uses prop_36)
- **step12:** AH = |(a─d)| * |(d─b)| (rectangle area)
- **step13:** |(d─h)| = |(d─b)| (parallel line property)

Look at step6, step9, step11 for patterns of how the agent decomposed complex proofs.
