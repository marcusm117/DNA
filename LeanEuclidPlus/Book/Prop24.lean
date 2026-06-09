import SystemE
import Book.Prop03
import Book.Prop04
import Book.Prop05
import Book.Prop12
import Book.Prop13
import Book.Prop17
import Book.Prop19
import Book.Prop23
import Book.Prop26

namespace Elements.Book1

/-- Degenerate SSA leaf of `proposition_24`: the construction point `g` lands exactly
on line `EF`, so `e, f, g` are collinear (the SSA-ambiguous configuration Euclid omits).
Stated with conclusion `|e─g| > |e─f|`; the caller has `|b─c| = |e─g|` in context.

Proof: `e, f, g` collinear on `EF` (step 1); ray `d→f` is interior to `∠e:d:g`, so line
`DF` separates `e` from `g` (steps 2–3, via `pasch_4`), giving `between e f g`; segment
addition then yields `|e─g| > |e─f|` (step 4). -/
theorem helper_24_ssa_degenerate : ∀ (d e f g : Point) (DE EF DF DG EG : Line),
  formTriangle d e f DE EF DF ∧
  d.onLine DG ∧ g.onLine DG ∧
  e.onLine EG ∧ g.onLine EG ∧
  g.onLine EF ∧
  |(d─f)| = |(d─g)| ∧
  (∠ e:d:g > ∠ e:d:f) ∧
  g.sameSide f DE ∧
  ¬(d.sameSide g EF) →
  |(e─g)| > |(e─f)| :=
by
  euclid_intros
  -- Step 1: e, f, g are collinear (all on line EF).
  --   e, f on EF from formTriangle; g on EF is the case hypothesis.
  euclid_assert (e.onLine EF)
  euclid_assert (f.onLine EF)
  euclid_assert (g.onLine EF)
  -- Step 2: ray d→f is interior to ∠e:d:g  (captured as f.sameSide e DG).
  --   g.sameSide f DE puts f, g on the same side of ray d→e; with ∠e:d:f < ∠e:d:g
  --   the smaller ray d→f lies between d→e and d→g.
  euclid_assert (f.sameSide e DG)
  -- Step 3: f lies between e and g.
  --   Ray d→f interior to ∠e:d:g ⟹ line DF separates e and g.
  --   f on both DF and EF; pasch_4 on line EF then gives between e f g.
  euclid_assert ¬(e.sameSide g DF)
  euclid_apply (pasch_4 e f g DF EF)
  euclid_assert (between e f g)
  -- Step 4: between e f g ⟹ |e─f| + |f─g| = |e─g| with |f─g| > 0, so |e─g| > |e─f|.
  euclid_finish

theorem proposition_24 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (|(a─b)| = |(d─e)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c > ∠ e:d:f) →
  |(b─c)| > |(e─f)| :=
by
  euclid_intros
  euclid_apply (proposition_23' d e a b c f DE AB AC) as g'
  euclid_apply (line_from_points d g') as DG
  euclid_apply (extend_point_longer DG d g' (a─c)) as g''
  euclid_apply (proposition_3 d g'' a c DG AC) as g
  euclid_apply (line_from_points e g) as EG
  euclid_apply (line_from_points f g) as FG
  euclid_apply (proposition_4 a b c d e g AB BC AC DE EG DG)
  euclid_apply (proposition_5' d g f DG FG DF)
  by_cases (d.sameSide g EF)
  · -- Isosceles △dfg (|d─f| = |d─g|): base angles equal (from proposition_5' above).
    euclid_assert (∠ d:g:f = ∠ d:f:g)
    -- f lies inside ∠e:d:g: g was built (prop_23') on f's side of DE with ∠e:d:g = ∠b:a:c > ∠e:d:f.
    euclid_assert (g.sameSide f DE)
    -- `f.sameSide e DG` is not directly reachable by SMT (angle-ineq ↛ ray-inside without help).
    -- Derive it via triple_incidence_2 on the three rays d→e (DE), d→f (DF), d→g (DG):
    -- line DF separates e and g (f is angularly between them), and g ∉ DF.
    euclid_assert ¬(g.onLine DF)
    euclid_assert ¬(e.sameSide g DF)
    euclid_apply (triple_incidence_2 DE DF DG d e f g)  -- e.sameSide f DG
    euclid_assert (f.sameSide e DG)
    euclid_assert (d.sameSide e FG)
    -- Ray g→e lies inside ∠d:g:f, splitting it: ∠dgf = ∠dge + ∠egf  ⟹  ∠egf < ∠dgf = ∠dfg.
    euclid_apply (sum_angles_onlyif g d f e DG FG)
    euclid_assert (∠ d:f:g > ∠ e:g:f)
    -- Ray f→d lies inside ∠e:f:g, splitting it: ∠efg = ∠efd + ∠dfg  ⟹  ∠efg > ∠dfg > ∠egf.
    euclid_apply (sum_angles_onlyif f e g d EF FG)
    euclid_assert (∠ e:f:g > ∠ e:g:f)
    euclid_apply (proposition_19 e f g EF FG EG)
    euclid_finish
  · -- Omitted by Euclid.  We split on whether g lands exactly on line EF.
    euclid_assert (g.sameSide f DE)
    euclid_assert ¬(g.onLine DF)
    euclid_assert ¬(e.sameSide g DF)
    by_cases g.onLine EF
    · -- Degenerate leaf: g exactly on EF ⟹ e, f, g collinear.  This is the SSA-ambiguous
      -- configuration; the *order* of e,f,g on the line is precisely the goal |e─f| < |e─g|,
      -- so it cannot be derived from collinearity alone.  The crossbar argument closes it:
      -- ray d→f is interior to ∠e:d:g, so f is between e and g on EF — see
      -- `helper_24_ssa_degenerate` above.  prop_4 gave |b─c| = |e─g|, so euclid_finish lifts
      -- the lemma's |e─g| > |e─f| to the goal.
      euclid_apply (helper_24_ssa_degenerate d e f g DE EF DF DG EG)
      euclid_finish
    · -- Non-degenerate: g not on EF.  Extend FG beyond f to h (between g f h).  Then f, being
      -- on both EF and DF, separates g from h across both lines, which wires the angle algebra.
      euclid_apply (extend_point FG g f) as h          -- between g f h ; h.onLine FG
      euclid_assert ¬(g.onLine DF)
      euclid_assert ¬(e.onLine DF)
      euclid_assert ¬(h.onLine DF)
      euclid_assert ¬(d.onLine EF)
      euclid_assert ¬(h.onLine EF)
      euclid_assert ¬(g.onLine EF)
      euclid_assert (g.sameSide f DE)

      -- f between g,h and f on both EF,DF ⟹ g,h opposite across both (pasch_3).
      euclid_apply (pasch_3 g f h EF)                  -- ¬(g.sameSide h EF)
      euclid_apply (pasch_3 g f h DF)                  -- ¬(g.sameSide h DF)
      euclid_assert ¬(e.sameSide g DF)
      -- two pairs already ¬sameSide ⟹ third forced (same_side_pigeon_hole).
      euclid_apply (same_side_pigeon_hole d g h EF)    -- ⟹ d.sameSide h EF
      euclid_assert (d.sameSide h EF)
      euclid_apply (same_side_pigeon_hole e g h DF)    -- ⟹ e.sameSide h DF
      euclid_assert (e.sameSide h DF)

      -- Two supplementary pairs along FG + the additivity splitting ∠d:f:e at ray f→h.
      -- LP-verified: these linearly force ∠e:f:g > ∠e:g:f.
      euclid_apply (proposition_13 d f g h DF FG)      -- ∠g:f:d + ∠d:f:h = 2∟
      euclid_apply (proposition_13 e f g h EF FG)      -- ∠g:f:e + ∠e:f:h = 2∟
      euclid_apply (sum_angles_onlyif f d e h DF EF)   -- ∠d:f:e = ∠d:f:h + ∠h:f:e
      euclid_apply (proposition_17 d g e DG EG DE)     -- ∠d:g:e + ∠g:e:d < 2∟
      euclid_apply (proposition_17 d f e DF EF DE)     -- ∠d:f:e + ∠f:e:d < 2∟
      euclid_assert (∠ e:f:g + ∠ g:f:d + ∠ d:f:e = ∟ + ∟ + ∟ + ∟)
      euclid_assert (∠ e:f:g > ∠ e:g:f)
      euclid_apply (proposition_19 e f g EF FG EG)
      euclid_finish

end Elements.Book1
