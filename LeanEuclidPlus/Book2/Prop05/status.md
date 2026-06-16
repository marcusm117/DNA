
# June 16, 3:46pm:
```
(leaneuclid) (base) taddmao@comps3:~/code/autoform/DNA/LeanEuclidPlus$ python3 scripts/check_step.py Book2/Prop05 --check                                                                                                                                                               
OK: Book2/Prop05 structurally sound â 63 node(s), naming law holds, every node has a backing file, every file carries the 30s cap, nothing pre-wired, no stray sorry, every cited [Prop.~B.N] satisfied (construction or helper-cone).
(leaneuclid) (base) taddmao@comps3:~/code/autoform/DNA/LeanEuclidPlus$ python3 scripts/check_step.py Book2/Prop05 --all
[check_step --all] bottom-up audit of 63 node(s) / 66 call-site(s) in Book2/Prop05 (sub-nodes before their parents):
  â step1: SP[isolated] + P (leaf, zero-sorry)
  â step2: SP[isolated] + P (leaf, zero-sorry)
  â step3: SP[isolated] + P (leaf, zero-sorry)
  â step4: SP[isolated] + P (leaf, zero-sorry)
  â step5: SP[isolated] + P (leaf, zero-sorry)
  â step6_big_eoff: SP[isolated] [4 call sites] + P (leaf, zero-sorry)
  â step6_doffce: SP[isolated] + Combine (container)
  â step6_boffef: SP[isolated] + Combine (container)
  â step6_boffdg: SP[isolated] + P (leaf, zero-sorry)
  â step6_bmf_hoffab: SP[isolated] + P (leaf, zero-sorry)
  â step6_eoffdg: SP[isolated] + P (leaf, zero-sorry)
  â step6_hoffef: SP[isolated] + P (leaf, zero-sorry)
  â step6_kmef: SP[isolated] + P (leaf, zero-sorry)
  â step6_dgbf: SP[isolated] + P (leaf, zero-sorry)
  â step6_doffbf: SP[isolated] + P (leaf, zero-sorry)
  â step6_hoffbf: SP[isolated] + P (leaf, zero-sorry)
  â step6_foffkm: SP[isolated] + P (leaf, zero-sorry)
  â step6_ssbd: SP[isolated] + P (leaf, zero-sorry)
  â step6_sscl: SP[isolated] + P (leaf, zero-sorry)
  â step6_sshg: SP[isolated] + P (leaf, zero-sorry)
  â step6_sshl: SP[isolated] + P (leaf, zero-sorry)
  â step6_big_ss: SP[isolated] + Combine (container)
  â step6_big: SP[isolated] + Combine (container)
  â step6_bmf_bopp: SP[isolated] + P (leaf, zero-sorry)
  â step6_bmf_bhe: SP[isolated] + P (leaf, zero-sorry)
  â step6_bmf_fse: SP[isolated] + P (leaf, zero-sorry)
  â step6_bmf_opp: SP[isolated] + Combine (container)
  â step6_bmf: SP[isolated] + Combine (container)
  â step6_par1: SP[isolated] + P (leaf, zero-sorry)
  â step6_par2: SP[isolated] + P (leaf, zero-sorry)
  â step6_cdhl: SP[isolated] + P (leaf, zero-sorry)
  â step6_hmfg: SP[isolated] + P (leaf, zero-sorry)
  â step6_compl: SP[isolated] + P (leaf, zero-sorry)
  â step6_lhs: SP[isolated] + P (leaf, zero-sorry)
  â step6_rhs: SP[isolated] + P (leaf, zero-sorry)
  â step6: SP[isolated] + Combine (container)
al check step node, just does sf and sp if not leaf? while --subtree does entire thing? is --subtree not documented in this file?  â step7 (Book2/Prop05/step7.lean): P FAILED â leaf backing file did not build (or hit the 30s cap â decompose).

[faithful_lib] build of Book2.Prop05.step7 exceeded 30s wall clock â TOO BIG. DECOMPOSE into more backing files; NEVER raise the cap. Last output before the kill (what it was elaborating when it stalled):
(leaneuclid) (base) taddmao@comps3:~/code/autoform/DNA/LeanEuclidPlus$ al check step node, just does sf and sp if not leaf? while --subtree does entire thing? is --subtree not documented in this file?

```

