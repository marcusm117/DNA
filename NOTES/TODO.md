# CURR
- make sure to prepare to delete Book/ . Currently Book3 is using it, and we should make it use things in Book1/ or Book1Vairants thing similar toi how book 1 imports. we should do it immediately so agents do not get confused. and a checker that they can only import these ones.

## Prove last done
- 6

## Map last done (including assumption):
- 6
(none except 1 is saved, so remember to save in batch. assumptions done as we go though)


# Naming is off
- Proposition 14 has a skip in naming for steps. Need to refactor this. The proof logic is identical but just name change.
- Another propostion has same issue as above in book 2 somewhere


# Immediate
- Look at "ommited by euclid in book 2" and see if it is geuininly ommited
- all of book 1 mappings. up to 10 is now done.
- Book 1 REQUIRES assumption always so super faithful and we quantify the gap with smt timeout. book 2 is lax on this, so we need to fix this after.
- For the above 6 and 14 need to fix from book 1, and all of book 2 need to check.

## WTS errors
 Phase-A only — clean conversions (no backing file for the WTS step; just swap to euclid_wts +
 rewrite the tail to assemble from the real component steps + re---save):

 ┌──────────────┬────────┬───────────────────────────────────────────────────┬─────────────────────┐
 │     Prop     │  loc   │                 current WTS claim                 │        tail         │
 ├──────────────┼────────┼───────────────────────────────────────────────────┼─────────────────────┤
 │ Book1/Prop09 │ 1.9.6  │ step6 : ∠ b:a:f = ∠ c:a:f                         │ exact ⟨hfa, step6⟩  │
 ├──────────────┼────────┼───────────────────────────────────────────────────┼─────────────────────┤
 │ Book1/Prop10 │ 1.10.3 │ step3 : between a d b ∧ |(a─d)| = |(d─b)|         │ exact ⟨d, step3⟩    │
 ├──────────────┼────────┼───────────────────────────────────────────────────┼─────────────────────┤
 │ Book1/Prop11 │ 1.11.5 │ step5 : ∠ a:c:f = ∟                               │ exact ⟨hfAB, step5⟩ │
 ├──────────────┼────────┼───────────────────────────────────────────────────┼─────────────────────┤
 │ Book1/Prop12 │ 1.12.5 │ step5 : h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) │ exact ⟨h, step5⟩    │
 └──────────────┴────────┴───────────────────────────────────────────────────┴─────────────────────┘

 Phase-B / done — the assert-then-reprove cases (convert removes a REDUNDANT monolithic helper, but the
 prop is currently green so this is a re-vet, not urgent):

 ┌──────────────┬────────┬────────────────────────────────────────────────────────────────────────┬───────────────┐
 │     Prop     │  loc   │                      WTS step / redundant helper                       │ re-derived by │
 ├──────────────┼────────┼────────────────────────────────────────────────────────────────────────┼───────────────┤
 │ Book2/Prop04 │ 2.4.13 │ step13 (4 right-angles) via helper_2_4_step13 — DONE/vetted prop       │ steps 14–18   │
 ├──────────────┼────────┼────────────────────────────────────────────────────────────────────────┼───────────────┤
 │ Book2/Prop11 │ 2.11.8 │ step8 (rect = square) via helper_2_11_step8 — Phase-B, step8 certified │ steps 9–20    │
 └──────────────┴────────┴────────────────────────────────────────────────────────────────────────┴───────────────┘
