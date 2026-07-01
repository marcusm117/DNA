---
name: euclid-figures
description: >
  Reference of recurring System-E figure-reasoning proof RECIPES for Book-2 rectangle-decomposition
  proofs (LeanEuclidPlus): the goal-shapes that come up over and over — sameSide, point-off-a-line,
  line-distinctness, betweenness via pasch, formParallelogram/formTriangle assembly, rectangle/sum
  area, and the parallel/angle props. Consult it from `prove-euclid`'s P step when you hit one of these
  shapes. For off-line / sameSide / area-recast / right-angle it points at an importable `Helpers/`
  LEMMA (one `euclid_apply`, no hand-built leaf); for betweenness / figure-assembly / proposition-props
  it gives the axiom CHAIN to re-prove against YOUR figure.
---

# Euclid figure recipes — "IF YOU NEED TO PROVE THIS, TRY THIS CHAIN"

This is **half library, half recipe book — and the split matters.**

- For the **off-line (Family 1)**, **line-distinctness (Family 2)**, **sameSide (Family 3)**,
  **area-recast (Family 6)**, **right-angle-from-co-interior (Family 7)**, **parallel-transitivity
  (Family 7)**, and **corresponding-angles (Family 7)** shapes, there is
  now an **importable lemma** in `LeanEuclidPlus/Helpers/{OffLine,SameSide,Area,RightAngle,Parallel,Angle,Pasch}.lean`.
  These shapes turned out NOT to be irreducibly figure-specific: each needs only 3–5 LOCAL atomic
  incidence facts (`p.onLine L`, `¬(p.onLine L)`, `p≠q`, `¬(L.intersectsLine M)`, …) — exactly what the
  parent already supplies — so a generic lemma takes those atoms as hypotheses and does NOT thread the
  whole figure. **Use the library lemma FIRST**; the axiom chain under each of those families is the
  FALLBACK for a shape no sibling covers. **One `euclid_apply` of a `Helpers/` lemma replaces a
  whole hand-built leaf — and is applied INLINE in the container with NO backing file** (see the
  `faithful-prove` LIBRARY EXCEPTION); this is how a step that was ~10 backing files collapses to ~1–3.
- For **figure-assembly (Family 5)** and the remaining **proposition props (Family 7:
  corresponding-angles, isosceles)** shapes, the facts ARE genuinely figure-specific (they thread which
  assembly, which transversal), so those families STAY recipes — the chains below are what you write
  against your own points, and those leaves legitimately stay as backing files.
- **betweenness/pasch (Family 4) is a HYBRID:** deriving the preconditions (which points are
  opposite/between which, the off-line facts) is figure-specific and stays a recipe — but the final bare
  `pasch_N` application is now wrapped in `Helpers/Pasch.lean` (`sameSide_of_between` for pasch_2,
  `not_sameSide_of_between` for pasch_3, `between_of_not_sameSide` for pasch_4). Use the wrapper for that
  last line; write the precondition chain against your own points as before.

**Extensibility law:** when you hand-build a NEW recurring off-line/sameSide/right-angle/area variant
(a flipped orientation, a different witness position), do NOT leave it as a one-off leaf — **PROMOTE it
to a sibling lemma** in the relevant `Helpers/` file (every mechanism has 2–3 orientation/witness
forms; match the ATOM your parent literally has, or add the sibling). The library grows; the file count
per step does not.

Each recipe entry still tells you the **axiom chain that has worked** for that goal-shape across the done
Prop01/02/03 (and Prop04's certified leaves) — you write the chain against your own points and let the
build judge it.

**How to use this (inside `faithful-prove`'s recursive SF/SP/P loop, via `prove-euclid`):**
- Hit a sub-goal whose shape matches a **LIBRARY box** (off-line / sameSide / area-recast / right-angle /
  parallel-trans) → discharge it INLINE: `import Helpers.<File>` (permanent) +
  `have <sub> : <goal> := <lemma> objs… (by assumption)…`. NO `:= by sorry`, NO backing file, NO
  script-wired node. If no sibling matches your atom-orientation, PROMOTE one into the Helpers file first.
- Hit a sub-goal whose shape matches a **RECIPE** (betweenness / assembly / corresponding-angles /
  isosceles) → introduce it as a `have <sub> : <goal> := by sorry` node, then prove its backing file with
  the chain here. Recurse if the chain needs its own sub-facts.
- The chains are **shapes, not substitutions** — match the GEOMETRY (which line is the transversal, which
  points are off which line), not the letters. A wrong instantiation simply fails SP/P; nothing unsafe is
  committed. That is exactly why this is recipes and not copy-paste bodies.
- All the usual rules still hold (`prove-euclid`): one fact per node, ≤30s, derive-don't-assume, replace
  SMT search with explicit `euclid_apply`. These recipes ARE rule #8 (explicit application) made concrete.

Look up exact signatures with `python3 scripts/find.py` (the sanctioned smart-grep over the declaration
DB — `--mentions <sym>`/`--concludes <sym>`/`--consumes <sym>`/`--name "<glob>"`, combinable), then
`Read` the printed `source` line; the relevant axioms live in
`SystemE/Theory/Inferences/{Diagrammatic,Transfer,Metric}.lean` and `Relations.lean`. Every recipe names
≥1 real file it's drawn from — open it to see the chain in context. (`grep` is hook-blocked here.)

---

## FAMILY 1 — point off a line  (`¬ p.onLine L`)
The bread-and-butter precondition for almost everything else (distinctness, sameSide, triangle/pgram).

> **LIBRARY FIRST — `Helpers/OffLine.lean`.** Match your goal to one of these and `euclid_apply`
> it (atomic hyps discharge by `assumption`); fall to the chains below only if no sibling fits — and if
> you hand-build a new variant, PROMOTE it here.
> - `offLine_of_parallel x w L M` — `x∈L`, witness `w∈M` off `L`, `¬(M.intersectsLine L)` ⟹ `¬(x∈M)`.
>   Parallel in the flipped orientation `¬(L.intersectsLine M)`: `offLine_of_parallel'` (same args).
> - `offLine_of_parallel_simple x L M` — NO off-line witness, but takes `L ≠ M` directly: `x∈L`, `L≠M`,
>   `¬(L.intersectsLine M)` ⟹ `¬(x∈M)`. (The `L≠M` is ESSENTIAL — without it `L=M` is a countermodel;
>   the parallel alone does NOT force `x` off `M`.) Flipped `¬(M.intersectsLine L)`: `offLine_of_parallel_simple'`.
> - `offLine_of_two_points x c w L M` — `x,c` distinct on `L`; `c∈M`; witness `w∈M` off `L` ⟹ `¬(x∈M)`
>   (being on `M` would equate `L=M`). Witness on the CARRIER instead (`w∈L` off `M`): `offLine_of_two_points'`.
> - `offLine_of_right_angle a b d L` — `a,b∈L`, `a≠b`, `a≠d`, `∠b:a:d=∟` ⟹ `¬(d∈L)`.
>
> The hand-chains below are the FALLBACK / the proof these lemmas encapsulate. Their `Ref:` files
> (`step6_foffkm`, `step6_doffbf`, the Prop04 leaves) are the ⟨OLD HAND FORM⟩ — keep them as STRUCTURE
> references only; the model for these facts is now the one-line library call, NOT a re-typed chain.

- **Off a PARALLEL line** (p is on a line `M`, `M ∦ L`, so p can't be on `L`): `by_contra`, then
  `intersection_lines_common_point p L M` (a shared point forces `L`,`M` to meet — contradicting
  `M ∦ L`), `euclid_finish`. *Ref: `Book2/Prop01/step5_ss_bg_ch.lean:17-24` (the `hboff`/`hgoff` sub-haves).*
- **Off a line because being on it would EQUATE two distinct lines**: `intro hon`;
  `euclid_apply (two_points_determine_line p q L M)` to get `L = M`; `rw` it and derive a contradiction
  from the now-collapsed collinearity (e.g. a right angle that can't hold on a straight line).
  *Ref: `Book2/Prop04/step5_cnad.lean`, `Book2/Prop04/step9_knab.lean`.*
- **Off a line from a right-angle + collinearity contradiction**: `intro hon`; `euclid_finish` (the
  contradiction — e.g. `a,b,d` collinear on `AB` with `∠b:a:d = ∟` — is small enough for the solver once
  the point is forced on the line). *Ref: `Book2/Prop04/step8_dnab.lean`.*
- GOTCHA — **`intersection_lines_common_point` REQUIRES `L1 ≠ L2` already in context.** Without it the
  SMT solver searches for distinctness and reliably times out — even in a 3-line file. The fix is always:
  establish `L1 ≠ L2` from an off-line anchor BEFORE the call:
  ```lean
  have hL1neL2 : L1 ≠ L2 := fun heq => hpoffL2 (heq ▸ hpL1)
  euclid_apply (intersection_lines_common_point p L1 L2)
  euclid_finish
  ```
  Find the anchor by asking: which point is on `L1` and NOT on `L2`? That's your `p`. If no such point
  is immediately in context, make it a sibling sub-node first (Family 1, off-a-parallel-line recipe).
  *Ref: `Book2/Prop05/step6_foffkm.lean` (hKMneEF first), `Book2/Prop05/step6_doffbf.lean` (hDGneBF),
  `Book2/Prop01/step5_ss_bg_ch.lean:17-24`.*
- GOTCHA: keep the signature SLIM — these are trivial facts; a bloated context makes even `euclid_finish`
  search. If an off-line leaf times out you have a context-size problem, not a hardness problem (slim
  the hyps, don't add depth).

## FAMILY 2 — two lines distinct  (`L ≠ M`)

> **LIBRARY — `Helpers/OffLine.lean`** for the off-line-anchor shape (the one that recurs ~60× as an
> inline term across Prop04–09 and is the precondition feedstock for `not_intersects_trans`'s three
> line-≠ args and the no-witness off-line / sameSide siblings):
> `line_ne_of_offLine p L M` — `p.onLine L`, `¬(p.onLine M)` ⟹ `L ≠ M`. Pure term, zero SMT. For the
> flipped `M ≠ L` use `(line_ne_of_offLine p L M …).symm`. (Equivalent to the hand term below — use
> whichever reads cleaner; both are free.)

- **From an off-line point** (cheapest): if you already have `¬p.onLine M` and `p.onLine L`, then
  `L ≠ M` is the term `fun h => hpoffM (h ▸ hpL)` (or `line_ne_of_offLine p L M hpL hpoffM` from the
  library box). No tactic, no search. *Ref: `Book2/Prop04/step9_par.lean:29`.*
- **OFF-BASE ANCHOR** for the `euclid_finish` route: supply a point on EACH line that sits OFF the shared
  base, so distinctness proves fast instead of searching the whole figure (e.g. `f` on `BF` off `BC`
  witnesses `BF ≠ BC`). *Ref: the `f`/`hfoffBC` binders threaded through `Book2/Prop01/step6_pgram.lean`.*
- GOTCHA: distinctness is a precondition of `proposition_30`, `formTriangle`, and most pgram assembly —
  derive the needed `L ≠ M` facts as small leaves/terms FIRST so the big call has them in hand.
- GOTCHA — **`intersectsLine` is NOT definitionally symmetric; flip with a TERM, not `euclid_finish`.**
  `intersection_symm L M : L.intersectsLine M → M.intersectsLine L`. To turn a context `¬(M.intersectsLine L)`
  into the `¬(L.intersectsLine M)` a lemma/prop wants, write the term `fun h => hML (intersection_symm L M h)`
  — do NOT `euclid_apply (intersection_symm …); euclid_finish` (it fails "Could not prove False"). Mind the
  arg order: `intersection_symm L M` proves `L∩M → M∩L`. *Ref: `Book2/Prop10/step6.lean` (`hCEFD`).*

## LINES MEET — `L.intersectsLine M`  (Euclid's Postulate 5 / "produced … will meet")
The shape behind every "being produced, the lines will meet at G" sentence (e.g. II.10), and the
precondition of `intersection_lines L M as g`.
> **NO Post-5 axiom exists.** `find.py --concludes intersectsLine` returns only `intersection_lines_opposing`
> (two points on M on OPPOSITE sides of L) and `intersection_lines_common_point` (a shared point + `L≠M`).
> When the crossing is by PRODUCTION (the meet point G is beyond the named points, so every named point of
> each line is on the SAME side of the other), `intersection_lines_opposing` does NOT apply with the named
> points, and a THIN `euclid_finish` (just the `<2 right angles` sum) **FAILS** — there is no rule
> "converging lines meet".
- **THE FIX: hand `euclid_finish` the WHOLE figure, not just the angle sum.** With the perpendicular,
  BOTH parallels (`¬EF∩AD`, `¬FD∩CE`), the betweenness, and the co-interior facts (`∠CEF+∠EFD=2∟`,
  `∠FEB+∠EFD<2∟`) all in the leaf's context, `euclid_finish` DOES derive `EB.intersectsLine FD` — the
  solver reconstructs the crossing from the full diagram. The lesson generalizes: for a meeting goal,
  slim NOTHING — give the leaf the rich figure context. *Ref (PROVEN): `Book2/Prop10/step8.lean`
  (thin context fails, full-figure context succeeds); `step7.lean` (the `<2∟` inequality, same rich-context
  `euclid_finish` derives the interior-ray ordering).*
- The follow-on "they meet" sentence just consumes the meeting (`:= hmeet`); the `as g` construction then
  fires. *Ref: `Book2/Prop10/step9.lean`.*

## FAMILY 3 — same side of a line  (`p.sameSide q L`)

> **LIBRARY FIRST — `Helpers/SameSide.lean`** (the single biggest recurring shape in Book 2, ~60
> leaves). Match and `euclid_apply`; fall to the chain only if no sibling fits; PROMOTE new variants.
> - `sameSide_of_parallel p q w L M` — `p,q∈L`; witness `w∈M` off `L`; `¬(M.intersectsLine L)` ⟹ `p.sameSide q M`.
> - `sameSide_of_parallel' p q u L M` — witness on the CARRIER: `p,q,u∈L`; `u∉M`; `¬(L.intersectsLine M)`
>   (covers `u=p`, the point itself as witness).
> - `sameSide_of_parallel_both p q L M` — NO off-line witness, takes `L ≠ M` directly: `p,q∈L`, `L≠M`,
>   `¬(L.intersectsLine M)` ⟹ `p.sameSide q M`. (Like the off-line no-witness form, `L≠M` is ESSENTIAL —
>   `L=M` is otherwise a countermodel.) The simplest rectangle shape once `L≠M` is in hand.
>
> For the segment-endpoint (`pasch_2`) shape below, the final call is now `Helpers/Pasch.lean`'s
> `sameSide_of_between` (and `not_sameSide_of_between` for the `pasch_3` opposite-sides shape) — use it for
> that line; deriving its `between`/off-line preconditions is still figure-specific.

- **Two points on a line `M ∦ L`, same side of `L`** (the workhorse): prove `¬p.onLine L` and
  `¬q.onLine L` (Family 1), then `by_contra hns`; `euclid_apply (intersection_lines_opposing p q L M)`;
  `euclid_finish` (opposing across `L` would make `M` cross `L`, contradicting `M ∦ L`). Add
  `euclid_apply (intersection_symm L M)` if the non-intersection fact you hold is oriented the other way
  (`¬M.intersectsLine L` vs `¬L.intersectsLine M`). *Ref (PROVEN, full chain):
  `Book2/Prop01/step5_ss_bg_ch.lean:15-27`; also `Book2/Prop01/step6_pgram.lean:21-26`,
  `Book2/Prop03/step6_sameside.lean`, `Book2/Prop04/step9_csg.lean`.*
- **Segment endpoint on the line** (`p.sameSide q L` where one segment end is ON `L`): if `r` is on `L`,
  `between r p q` (or `between q p r`), and `p,q ∉ L`, then `euclid_apply (pasch_2 r p q L)`;
  `euclid_finish`. *Ref: `Book2/Prop04/step5_ss.lean:18-21` (`c.sameSide a BD` via `pasch_2 b c a BD`).*
- GOTCHA: **`intersection_lines_opposing` and `intersection_lines_common_point` both need `L1 ≠ L2`
  already in context** — same rule as Family 1's GOTCHA. Establish it first (term-mode from an off-line
  anchor), then the call + `euclid_finish` finishes in <10s.
- GOTCHA: `sameSide` is the lone HARD conjunct of `formParallelogram` — these are the leaves you extract
  before an area call (Family 6). Don't try to get `sameSide` out of an angle-split that itself needs it
  (circular — see prove-euclid CRUCIAL SUBTLETIES); go through betweenness/pasch instead.

## FAMILY 4 — betweenness of feet / crossing points  (`between p q r`)
The "a transversal foot / intersection point lands between two others" shape. **This is the
`between b g d`/`between b k e` shape the Prop04 agent stalled on — it is NOT hard with this chain.**
> HYBRID — deriving the preconditions (which points are opposite/between which) is figure-specific, so
> write that chain against your own points. But the final `pasch_N` application is now wrapped in
> `Helpers/Pasch.lean`: `not_sameSide_of_between a b c L` (pasch_3), `between_of_not_sameSide a b c L M`
> (pasch_4), `sameSide_of_between` (pasch_2) — end the chain with the wrapper instead of a bare `pasch_N`.
> The recipes below show the axiom-level chain (still the right shape for the precondition derivation).
- **Crossing point of two lines lies between two points** (`q = L ∩ GH`, want `between p q r` with
  `p,r` on `GH`): show `p,r` on OPPOSITE sides of `L`, then `euclid_apply (pasch_4 p q r L GH)`;
  `euclid_finish`. Get the opposite-sides fact from a point `x` on `L` that is `between p' r'` on a base
  line: `euclid_apply (pasch_3 p' x r' L)`. *Ref (PROVEN): `Book2/Prop01/step5_btw_glh.lean:21-25`
  (`pasch_3 b e c EL` → `pasch_4 g l h EL GH`); `Book2/Prop01/step5_btw_gkl.lean`.*
- **Diagonal/interior crossing** (`between b g d`, `g = CF ∩ BD`): same chain — `b,d` opposite sides of
  `CF` (one side via `pasch_3 a c b CF` since `c` on `CF` is `between a b`; the other side a `sameSide`
  sub-node), then `pasch_4 b g d CF BD`. *Ref: `Book2/Prop04/step5_bgd.lean:22-26` (note its
  `a.sameSide d CF` is its OWN sub-node — derive the sameSide separately, Family 3).*
- GOTCHA: `pasch_3` needs the middle point ON `L` and `between` the two outer points on a base line;
  `pasch_4` needs the two outer points on OPPOSITE sides of `L` and the crossing point on both `L` and
  the line they're on. Map every precondition before calling.

## FAMILY 5 — assemble a figure  (`formParallelogram …`, `formTriangle …`)
> **LIBRARY-ABLE — the assembly IS genericizable.** `formParallelogram a b c d …` from its ATOMS (the
> incidences + `≠`s + the one `sameSide` + the two `¬intersects`) is a generic, universally-quantified
> lemma — NOT whole-figure-threaded (the hyps are all atomic facts the parent supplies). A
> `mk_parallelogram`-style lemma in `Helpers/` (e.g. the shape of `Book2/Prop02/step5_hsq.lean`, which is
> already fully generic) can take those atoms and `euclid_finish` the remaining conjuncts. CAVEATS that
> make this a SMALLER win than off-line/sameSide, so it's lower-priority: (a) the hard hyp is still the
> `sameSide` — you derive THAT via `Helpers/SameSide.lean` (Family 3) regardless, and once you have it the
> inline `exact ⟨…, ss, …⟩` constructor is already cheap; (b) `formParallelogram` has vertex-ordering /
> orientation variants, so like off-line it needs a few siblings. So: promote a `mk_parallelogram` sibling
> when a shape recurs, but the everyday move is still "derive the sameSide (library), then inline-assemble."
- **`formParallelogram` — assemble, don't search.** Closing it with ONE fat `euclid_finish` over its ~10
  conjuncts (4 incidences + distinctness + the `sameSide` + two non-intersections) routinely blows 30s.
  Instead: derive the hard `sameSide` as its own sub-node (Family 3) and the `≠` facts (Family 2), then
  the incidences/distinctness are already in context — let `euclid_finish` close from atoms with nothing
  to search. (For an even tighter close, `refine ⟨…incidences…, ss_subnode, ?_, ?_⟩` and only
  `euclid_finish` the 1-2 parallel/orientation conjuncts.) *Ref (PROVEN): `Book2/Prop01/step6_pgram.lean`
  (the `hbsc` sameSide sub-have + `hgh : g ≠ h`, then `euclid_finish`); `Book2/Prop03/step6_par.lean`,
  `Book2/Prop04/step9_par.lean`.*
- **`formTriangle`** — three pairwise-distinct lines (Family 2) + the incidences, then `euclid_finish`.
  *Ref: `Book2/Prop04/step8_tri.lean`.*
- GOTCHA: REUSE a sibling's figure-fact rather than re-deriving. If an earlier step proved a
  `between`/`sameSide`/`formParallelogram` you need, take it as a HYPOTHESIS (it wires by `assumption`)
  — e.g. Prop03 step6 reuses step5's `between e d f`. Re-proving it is wasted depth.

## FAMILY 6 — area of a figure  (`rectangle_area`, `sum_parallelograms_area`)

> **LIBRARY — `Helpers/Area.lean`** for the parallelogram-area RECAST shape only:
> `parallelogram_area' a b c d AB CD AC BD` — from `formParallelogram a b c d …` proves the diagonal
> split `△a:c:d + △a:d:b = △b:a:c + △b:c:d` in one shot (the recurring step6_lhs/step6_rhs "complement"
> leaves); the call-site relabel is then a cheap symmetry `euclid_finish`. `rectangle_area` and
> `sum_parallelograms_area` themselves stay figure-specific recipes (their preconditions thread the
> figure) — chains below.

- **`rectangle_area`** (parallelogram with a right angle → `area = side·side`): the call's
  `formParallelogram` precondition is what times out, NOT the area algebra. So DECOMPOSE first — get
  `formParallelogram` (Family 5) and the right angle (Family 7) as sub-nodes, THEN
  `euclid_apply (rectangle_area …)`; `euclid_finish`. *Ref (PROVEN): `Book2/Prop01/step6.lean:23-26`
  (step6_rangle + step6_pgram sub-haves, then `rectangle_area b g c h BF CH BC GH`);
  `Book2/Prop03/step5.lean`, `Book2/Prop03/step7.lean`.*
- **`sum_parallelograms_area`** (cut a rectangle along a vertical → 4 sub-triangles sum to the halves):
  establish every foot-`between` (Family 4) and every `sameSide` (Family 3) as sub-nodes first, then one
  `euclid_apply` per cut, then `euclid_finish` telescopes. For a TWO-cut decomposition, call it once per
  cut (outer then inner). *Ref: `Book2/Prop01/step5.lean` (two `sum_parallelograms_area` calls after 5
  sameSide + 2 betweenness sub-nodes).*
- GOTCHA: a single oversized `euclid_apply (area_axiom …)` is DECOMPOSED, never re-permuted — re-running
  the same axiom with a different vertex/line order hoping one is cheaper is the forbidden
  restate-and-hope. Extract the precondition instead.

## FAMILY 7 — parallels & angles  (the cited Book-1 props)

> **LIBRARY — `Helpers/RightAngle.lean`** for the right-angle-from-co-interior shape:
> `right_angle_cointerior b d g h L1 L2 T` — `g,b∈L1` distinct, `h,d∈L2` distinct, `g,h∈T` distinct,
> `b.sameSide d T`, `¬(L1.intersectsLine L2)`, and ONE known right angle `∠g:h:d=∟` ⟹ `∠b:g:h=∟`.
> Wraps the `proposition_29'''''` rectangle-corner core (the caller still does its own orientation prep —
> which angle is the known-right one, via supplement/ray-rewrite). PROMOTE a new angle-wrapper here if a
> variant recurs.
>
> **LIBRARY — `Helpers/Parallel.lean`** for parallel-transitivity:
> `not_intersects_trans L1 L2 L3` — `¬(L1.intersectsLine L2)`, `¬(L2.intersectsLine L3)`, and the three
> pairwise `≠` (`L1≠L2`, `L2≠L3`, `L1≠L3`) ⟹ `¬(L1.intersectsLine L3)`, via `proposition_30`. Derive the
> three line-≠ as cheap off-line-anchor terms (`line_ne_of_offLine`, Family 2) first, then one `euclid_apply`.
>
> **LIBRARY — `Helpers/Angle.lean`** for the corresponding-angle-at-feet shape (recurs across the
> II.5/II.6/II.7 isosceles arguments — Prop05 step13_dhdb_corr, Prop06 step11_dmdb_corr, Prop07 step9_corr):
> `corresponding_angle b c d e h L1 L2 T` — `L1 ∥ L2` (`¬(L1.intersectsLine L2)`); transversal `T` through
> `b`, near foot `h∈L1`, far foot `e∈L2` with `between b h e`; `d∈L1`, `c∈L2` with `d.sameSide c T` ⟹
> `∠ d:h:b = ∠ c:e:b`. Atomic hyps. The conclusion orientation is Prop05's; Prop06/07 cut the SAME figure
> but close the rays to a differently-named far endpoint — **PROMOTE an orientation sibling** into Angle.lean
> when you hit one (identical body modulo which endpoint the rays close to), exactly as OffLine/SameSide carry
> siblings. The isosceles recipe below stays a figure-specific leaf — no library lemma.

- **Parallel transitivity** (`¬CF.intersectsLine BE` from `CF ∥ AD` and `AD ∥ BE`): ⟨OLD HAND FORM — use
  `not_intersects_trans` from the library box above; this is the chain it encapsulates⟩. The three lines
  pairwise distinct (Family 2), then `euclid_apply (proposition_30 CF BE AD)`; `euclid_finish`.
  *Ref: `Book2/Prop04/step9_cfbe.lean:14-20`, `Book2/Prop05/step7_dfpar_dgbf.lean`.*
- **Right angle from co-interior angles** (`∠b:c:h = ∟`): ⟨OLD HAND FORM — use `right_angle_cointerior`
  from the library box above; this is the chain it encapsulates⟩. Two parallels cut by a transversal, the
  co-interior angles sum to two right angles — `g.sameSide h BC` sub-node (Family 3), then
  `euclid_apply (proposition_29''''' g h b c BF CH BC)`; `euclid_finish` (the solver finishes the
  `∠g:b:c = ∠f:b:c = ∟` ray-rewrite). *Ref (PROVEN): `Book2/Prop01/step6_rangle.lean:24-33`.*
- **Corresponding angles** (`∠c:g:b = ∠a:d:b`): ⟨use `corresponding_angle` from the library box above
  when the figure matches its orientation; this is the chain it encapsulates / the FALLBACK for a
  different orientation⟩. `proposition_29''''` with the transversal `sameSide` (Family 3) + the interior
  `between` (Family 4) in hand, then a ray-coincidence `equal_angles` + symmetry `euclid_finish`.
  *Ref: `Book2/Prop04/step5_corr.lean`, `Book2/Prop05/step13_dhdb_corr.lean`,
  `Book2/Prop06/step11_dmdb_corr.lean`, `Book2/Prop07/step9_corr.lean` (the four orientations).*
- **Isosceles: equal base angles → equal sides** (`|b─c| = |c─g|`): build `formTriangle` (Family 5),
  recast the angle equality into prop-6 base-angle orientation with `angle_symm` (a real-valued rewrite,
  `rw [hstep7, hsym]`), then `euclid_apply (proposition_6 c g b CF BD AB)`; `euclid_finish`.
  *Ref (PROVEN): `Book2/Prop04/step8.lean:32-40`.*
- GOTCHA: cross-book props collide on short names — fully-qualify `Elements.Book1.proposition_M` and
  `import Book.PropM`. A cited `[Prop.~1.M]` is only RECORDED for the dependency check when it enters via
  `euclid_apply` (never term-mode `exact`) — see `faithful-prove`'s dependency-check section.

---

## THE FINAL COMBINE — `linarith` / `ring` ARE available (preferred for the arithmetic)
The last step of an area/length proof (conclusion = a linear combination of the per-step equations) is
closed with **`linarith`/`nlinarith`/`ring`** — Mathlib is a project dependency, so `import
Mathlib.Tactic.Linarith` (or `.Ring`) at the top of the backing file and use them. The SMT translator
behind `euclid_finish` chokes on exactly this pure-ℝ arithmetic (notably `2 * x` in hypothesis
position), so `linarith`/`ring` over the locked per-step equations is usually the *right* closer, not a
fallback. The lean-closer pattern still holds: end on a THIN closer (`linarith [...]` over named
`have h… : <equation>` facts, or a `rw [...]` chain), never a fat `euclid_finish` doing the geometry AND
the algebra at once — split the algebra out (one `have h… := by euclid_finish` per rewrite, then
`linarith`). Keep the GEOMETRY in the SMT path (`euclid_apply`/`euclid_finish` equalities as `have`s);
put the ARITHMETIC in Mathlib. *Ref: `Book2/Prop09/step10.lean` (`euclid_apply angle_symm` then `linarith`
for the `2·∠ = ∟ ⟹ ∠ = ∟/2` halving); `Book2/Prop01/step10.lean` (`euclid_finish` over 5 area-equations —
also valid); `Book2/Prop03/step8.lean` (`rw [← step5, step4, step6, step7]`).*

- **ANGLE-HALVING is a recurring `linarith` shape (Prop09 step10/step11/step12), NOT a library lemma.**
  From equal base angles `∠X = ∠Y` (isosceles, via prop_5/prop_6 + `angle_symm` to orient) and an
  angle-sum `∠X + ∠Y = ∟` (or `… = ∟ + ∟` minus a right angle, via prop_32), each base angle is `∟/2`:
  `have : 2 * (∠X) = ∟ := by linarith` then `linarith`. The SMT translator can't carry `∟/2`; keep the
  GEOMETRY (`angle_symm`, prop_5/_32 equalities) as `have`s and let `linarith` do the halving. It's two
  lines inline — do NOT extract a lemma (the content is the geometry, not the arithmetic). *Ref:
  `Book2/Prop09/step10.lean`, `step11.lean` (prop_5 base angles + prop_32 sum + `2*∠=∟` halve).*
- GOTCHA — **a `∠…=∟/2` (or `2*x`) fact ANYWHERE in a `euclid_finish` context CRASHES the translator**
  ("[Smt.Translator] Improper numeric"), even when the goal is pure geometry — because `euclid_finish`
  translates the WHOLE local context to SMT. So when a step CONSUMES a `∟/2` half-angle (e.g. a
  vertical-angle or remaining-angle step that takes `∠e:b:c=∟/2` as a hyp): prove the geometry part with
  the `∟/2` hyp **CLEARED** — `have hgeom : <pure angle eq> := by clear hhalf; euclid_apply …; euclid_finish`
  — then combine with `linarith [hhalf, hgeom]`. Never let the `∟/2` reach `euclid_finish`. (All of
  Prop09's halving uses `linarith` for exactly this reason.) *Diagnosed in `Book2/Prop10/step16.lean`
  (vertical angle `proposition_15`: the `∟/2` hyp crashed `euclid_finish` until cleared).*