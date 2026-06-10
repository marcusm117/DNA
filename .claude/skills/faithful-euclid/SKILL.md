---
name: faithful-euclid
description: >
  DEPRECATED / SPLIT. Making a Book-2 Euclid proof faithful is now TWO skills: `faithful-map`
  (Phase A — translate each sentence into a Lean claim type, in Book<N>/PropNN/Main.lean; stops for
  human review) and `faithful-prove` (Phase B + final gate — prove each Book<N>/PropNN/stepN.lean and
  verify). Use whenever the task is "make Book2/PropNN faithful": run `faithful-map` first, get human
  approval, then `faithful-prove`.
---

# faithful-euclid — split into faithful-map + faithful-prove

This skill was split so each phase is small and focused (the monolithic version leaked proving
concerns into the translation phase). Use:

1. **`faithful-map`** — Phase A. Translate Euclid's sentences into `euclid_sentence` claim types in
   `Book<N>/PropNN/Main.lean` (sorry-stub `stepN.lean` files). Pure translation, not proving. STOPS
   for human review + `scripts/check_steps.py --save`.
2. **(human reviews the claim types and approves.)**
3. **`faithful-prove`** — Phase B + final gate. Prove each `Book<N>/PropNN/stepN.lean` (delegates to
   `prove-euclid`), then run the authoritative `scripts/check_faithful.sh Book<N>`.

Operator guide: [../../../LeanEuclidPlus/FAITHFUL.md](../../../LeanEuclidPlus/FAITHFUL.md).
