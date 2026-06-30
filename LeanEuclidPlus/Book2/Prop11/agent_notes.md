# Prop11 (Euclid II.11) — faithful-prove agent notes

## Figure (from data/diagrams/11.png)
- Big square **ABDC** on AB: A top-left, B top-right, C bottom-left, D bottom-right.
  Lines: AB (top), CD (bottom, contains c,k,d), AC (left, contains f,a,e,c), BD (right).
- E = midpoint of AC (between a e c).
- F on line CA extended beyond A: order on AC is **c, e, a, f, f0** (f beyond a; f0 even further,
  the construction point; F=f with |ef|=|be|). `between c a f` is the key derived order fact.
- Small square **FGHA** on AF (proposition_46', opposite side of AC from x≈same side as b):
  F top-left, G top-right, H bottom-right (on AB), A bottom-left.
  Lines: FG (top, contains f,g), GH (right vertical, contains g,h,k — order between g h k), AH (=AB!).
- K = GH ∩ CD (bottom-right region). between g h k on GH.
- **AH = AB** (both ⊥ AC at A, h & b same side of AC) — proven in step16_ahab. h on AB ⟺ between a h b.

## Key reusable facts / leaves already built (step16 cone)
- `step8_pyth` (Book.Prop47): |eb|² = |ae|² + |ab|²  — reused by step9, step12, step16.
- `step9_eaf` : between e a f  (nlinarith magnitude; needs step8_pyth as hpy).
- `between c a f` : derive inline `by euclid_finish` from step9_eaf (between e a f) + between a e c.
- `step16_ahab` : AH = AB  (euclid_finish from ∠bac=∟, ∠fah=∟, ¬h.sameSide x, ¬x.sameSide b, between c a f).
- off-line leaves (use Helpers.OffLine `offLine_of_right_angle` / `offLine_of_two_points`):
  step16_ancd ¬a∈CD, step16_fncd ¬f∈CD, step16_fnab ¬f∈AB. Need |cd|=|ab|+a≠b for c≠d.
- `step16_fgcd` : ¬FG∩CD — Prop04-style proposition_30 leaf taking the 3 line-≠ + 2 ¬∩ as HYPS.
  Container builds the ≠ as zero-SMT `line_ne_of_offLine` terms + not needed (uses step16_fgcd leaf).
- `step16_par` : formParallelogram f c g k AC GH FG CD — sameSide via Helpers.SameSide
  `sameSide_of_parallel_both`; c≠k via `offLine_of_parallel c h AC GH` (h witness on GH off AC).

## rectangle_area recipe (THE area-step workhorse, Family 6)
`rectangle_area a b c d AB CD AC BD : formParallelogram .. ∧ ∠a:c:d=∟ →
   (area△a:c:d + area△a:b:d = |a-b|*|a-c|) ∧ (area△b:a:c + area△b:d:c = |a-b|*|a-c|)`.
- DECOMPOSE: formParallelogram (step._par) + right angle as sub-nodes, then term-mode
  `obtain ⟨h1,_⟩ := rectangle_area ..  ⟨par, rangle⟩; exact h1` — do NOT close with `euclid_finish`
  (it CHOKES on the product `|f-c|*|f-g| = |c-f|*|f-a|`). Recast lengths by `rw [segment_symmetric..]`
  BEFORE the obtain so the goal matches h1 literally.
- step16: rect FGKC = formParallelogram f c g k AC GH FG CD, right angle ∠f:g:k=∟. area = |c-f|*|f-a|.

## GOTCHAS
- `|(f─g)| = |(a─f)|` is the LITERAL context atom (reversed from the @assumption's |(a-f)|=|(f-g)|).
  Retyped the binder + Main @assumption comment to match (assumption is exact, no symmetry).
- euclid_finish can't get ¬p∈L from non-intersection alone — needs a geometric witness
  (right angle, or two-points-determine-line via an off-line witness). Use Helpers.OffLine lemmas.
- proposition_30 distinctness search times out in a big context — derive the 3 line-≠ as explicit
  terms (line_ne_of_offLine) and pass them in (Prop04 step9_cfbe pattern).

## STATUS: PHASE B COMPLETE — all 24/24 Main cones --subtree-certified, inputs fresh.
criterion-3 deps ✓ · no orphans ✓. The ONLY whole-prop blocker is integrity ✗ from
`Book2/Prop11/template/Main.lean` — a STRAY user reference file (the complete NON-faithful
alternate proof, with its OWN `theorem proposition_11`). It (a) is missing the 30s `set_option`
(fails integrity), and (b) would COLLIDE with the faithful Main.lean's `proposition_11` when Book2
builds (both are `Elements.Book2.proposition_11`). Must be removed/relocated by the human before the
final `--all` and Phase C. NOT touched by the agent (user artifact, git-tracked).

### Step recipes (1-23 + between_ahb)
- 1-8 done before this session. 9 = II.6 (proposition_6, between e a f magnitude). 10-15 = length/area
  algebra (euclid_finish/rw/linarith). 16 = rect FGKC (rectangle_area, FG∥CD via AH=AB+prop30, 8 leaves).
  17 = square ABDC (rectangle_area). 18 = transitivity (linarith). 19 = GNOMON (two sum_parallelograms_area
  + between g h k / c k d / a h b, 18 nodes). 20 = restate 19. 21 = HD=rect(AB,BH) (rectangle_area HBDK,
  ∠d:b:h via equal_angles, |dk|=|bh| via prop34). 22 = square FGHA (rectangle_area, ∠f:g:h given).
  23 = golden eq (linarith [20,21,22]). between_ahb = self-contained magnitude tower → between a h b
  (reused by 19, 21; derives |af|<|ab| internally so it's Main-suppliable).
