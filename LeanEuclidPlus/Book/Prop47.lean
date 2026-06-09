import SystemE
import Book.Prop04
import Book.Prop13
import Book.Prop14
import Book.Prop16
import Book.Prop17
import Book.Prop29
import Book.Prop30
import Book.Prop31
import Book.Prop41
import Book.Prop46

namespace Elements.Book1

/-
Common sub-fact for the hC11 / hC10 leaves of `helper_47_angle_dba_eq_fbc`, and for
`helper_47_e_sameSide_b_AC`.

TRUE (verified): `M ⊥ L` at `b`, `q` on `L`, ray `b→p` acute to `b→q` (∠p:b:q < ∟)
  ⟹ `p` on `q`'s side of the perpendicular `M`.

Proof by contradiction: if p,q opposite across M, the segment p─q meets M at some
point x; then x is on M, q is on L, and b is the L∩M foot, forcing ∠p:b:q ≥ ∟.
-/
theorem helper_47_sameSide_perp :
    ∀ (p q b r : Point) (L M : Line),
    q.onLine L ∧ b.onLine L ∧ b ≠ q ∧
    b.onLine M ∧ r.onLine M ∧ b ≠ r ∧
    L ≠ M ∧
    ¬p.onLine L ∧ ¬p.onLine M ∧
    (∠ q:b:r : ℝ) = ∟ ∧
    (∠ p:b:q : ℝ) < ∟ →
    p.sameSide q M :=
by
  euclid_intros
  by_contra hcon
  -- q is off M (q on L, q≠b, L≠M), p is off M, and they're not same-side ⟹ segment meets M.
  euclid_apply (line_from_points p q) as PQ
  euclid_apply (intersection_lines PQ M) as x
  -- x is the crossing point of segment p─q with M ⟹ x between p and q (pasch_4, sep line M)
  euclid_apply (pasch_4 p x q M PQ)
  have hbtw : between p x q := by euclid_finish
  -- x on perpendicular M (through b) and q on L ⟹ ∠q:b:x = ∟
  have hperp : (∠ q:b:x : ℝ) = ∟ := by euclid_finish
  -- ray b→x splits ∠p:b:q (x between p,q; b off line pq).  Derived, NOT via an angle axiom:
  --   pasch_2 turns the betweenness into the two sameSide facts that sum_angles_onlyif needs.
  have hsplit : (∠ p:b:q : ℝ) = (∠ p:b:x : ℝ) + (∠ x:b:q : ℝ) := by
    euclid_apply (line_from_points b p) as BP
    euclid_apply (line_from_points b q) as BQ
    euclid_apply (pasch_2 q x p BQ)   -- between q x p, q∈BQ, x∉BQ ⟹ x.sameSide p BQ
    euclid_apply (pasch_2 p x q BP)   -- between p x q, p∈BP, x∉BP ⟹ x.sameSide q BP
    euclid_apply (sum_angles_onlyif b p q x BP BQ)
    euclid_finish
  -- then ∠p:b:q = ∠p:b:x + ∟ ≥ ∟, contradicting ∠p:b:q < ∟
  euclid_finish

/-
Helper for Prop47  `e.sameSide b AC`.
Square BCDE on BC, opposite side from a; extend a─c to c' with exterior ∠b:c:c' > ∟.
Base angle ∠a:c:b < ∟, ∠b:c:e = ∟, so ray c→e stays on b's side of AC.
-/
theorem helper_47_e_sameSide_b_AC :
    ∀ (a b c d e c' : Point) (AB BC AC BD CE DE : Line),
    a.onLine AB ∧ b.onLine AB ∧ a ≠ b ∧
    b.onLine BC ∧ c.onLine BC ∧
    a.onLine AC ∧ c.onLine AC ∧
    AB ≠ BC ∧ BC ≠ AC ∧ AC ≠ AB ∧
    (∠ b:a:c : ℝ) = ∟ ∧
    (∠ a:c:b : ℝ) < ∟ ∧
    ¬e.onLine AC ∧
    b.onLine BD ∧ d.onLine BD ∧
    c.onLine CE ∧ e.onLine CE ∧
    d.onLine DE ∧ e.onLine DE ∧
    (∠ c:b:d : ℝ) = ∟ ∧ (∠ b:c:e : ℝ) = ∟ ∧
    (∠ b:d:e : ℝ) = ∟ ∧ (∠ c:e:d : ℝ) = ∟ ∧
    ¬d.sameSide a BC ∧
    ¬DE.intersectsLine BC ∧ ¬BD.intersectsLine CE ∧
    c'.onLine AC ∧ between a c c' ∧
    (∠ b:c:c' : ℝ) > ∟ →
    e.sameSide b AC :=
by
  euclid_intros
  -- Step 1: a.sameSide b CE  (perpendicular lemma: CE⊥BC at c, acute ∠a:c:b)
  euclid_apply (helper_47_sameSide_perp a b c e BC CE)
  -- Step 2: e.sameSide b AC  (triple_incidence_2 on lines CE,BC,AC at c)
  euclid_apply (triple_incidence_2 CE BC AC c e b a)
  euclid_finish

/-
Sub-lemma for `helper_47_between_blc`:  AL ∥ BD and BD ⊥ BC (∠c:b:d = ∟) ⟹ AL ⊥ BC,
i.e. the foot l' = AL ∩ BC makes a right angle:  ∠a:l':b = ∟.

Proof: proposition_29''' on parallels AL, BD with transversal BC (meeting at l', b) gives the
alternate-angle equality ∠a:l':b = ∠l':b:d; since l' lies on BC (ray from b toward c or its
opposite), ∠l':b:d = ∠c:b:d = ∟.
-/
theorem helper_47_AL_perp_BC :
    ∀ (a b c d l' : Point) (BC BD AL : Line),
    a.onLine AL ∧ l'.onLine AL ∧ a ≠ l' ∧
    b.onLine BC ∧ c.onLine BC ∧ l'.onLine BC ∧ b ≠ c ∧ b ≠ l' ∧
    b.onLine BD ∧ d.onLine BD ∧ b ≠ d ∧
    ¬a.onLine BC ∧ ¬d.onLine BC ∧
    ¬a.onLine BD ∧
    BC ≠ BD ∧ AL ≠ BD ∧
    (∠ c:b:d : ℝ) = ∟ ∧
    ¬AL.intersectsLine BD ∧
    a.opposingSides d BC →       -- a (apex) and d (square corner) on OPPOSITE sides of BC
    (∠ a:l':b : ℝ) = ∟ :=
by
  euclid_intros
  -- alternate angles: ∠a:l':b = ∠l':b:d  via proposition_29''' (parallels AL,BD; transversal BC)
  euclid_apply (proposition_29''' a d l' b AL BD BC)
  -- l' on BC and ∠c:b:d = ∟ ⟹ ∠l':b:d = ∟
  euclid_finish

/-
Helper for Prop47  precondition `between b l' c` of `sum_parallelograms_area`.

`AL` runs through apex `a`, parallel to the square sides `BD` (through b) and `CE`
(through c); `l' = AL ∩ BC`.  Since `AL ⊥ BC` (AL ∥ BD ⊥ BC) the foot `l'` makes a right
angle with `BC` (∠a:l':b = ∠a:l':c = ∟, robustly — supplement of a right angle is right).
With both base angles acute, the foot lands strictly between `b` and `c`.

Proof: negate, case-split the ordering of b,l',c (between_points).  Each bad ordering puts
`l'` outside [b,c]; then proposition_17 (a right angle + a positive angle in the foot
triangle < 2∟) and proposition_13 (straight line) force a base angle > ∟ — contradiction.
-/
theorem helper_47_between_blc :
    ∀ (a b c l' : Point) (AB BC AC BD CE AL : Line),
    a.onLine AB ∧ b.onLine AB ∧
    b.onLine BC ∧ c.onLine BC ∧ b ≠ c ∧
    a.onLine AC ∧ c.onLine AC ∧
    ¬a.onLine BC ∧
    AB ≠ BC ∧ AC ≠ BC ∧
    b.onLine BD ∧ c.onLine CE ∧
    (∠ a:b:c : ℝ) < ∟ ∧ (∠ a:c:b : ℝ) < ∟ ∧
    a.onLine AL ∧ l'.onLine AL ∧ l'.onLine BC ∧
    ¬AL.intersectsLine BD ∧ ¬AL.intersectsLine CE ∧
    ¬BD.intersectsLine CE ∧
    -- AL ⊥ BC at the foot l' (true in Prop47: AL ∥ BD, BD ⊥ BC):
    (∠ a:l':b : ℝ) = ∟ ∧ (∠ a:l':c : ℝ) = ∟ →
    between b l' c :=
by
  euclid_intros
  by_cases hbtw : between b l' c
  · exact hbtw
  · exfalso
    by_cases hb2 : between l' b c
    · -- l' beyond b: foot triangle a-l'-b has right angle at l' ⟹ ∠a:b:l' < ∟,
      --   but l'-b-c straight ⟹ ∠a:b:c = 2∟ - ∠a:b:l' > ∟, contradicting acute.
      euclid_apply (proposition_17 a l' b AL BC AB)
      euclid_apply (proposition_13 a b c l' AB BC)
      euclid_finish
    · -- otherwise the ordering is b-c-l' (c beyond): symmetric at vertex c.
      euclid_apply (proposition_17 a l' c AL BC AC)
      euclid_apply (proposition_13 a c b l' AC BC)
      euclid_finish

/-
Helper for Prop47  precondition `between d l e` of `sum_parallelograms_area`.

`l = AL ∩ DE`.  `d ∈ BD ∥ AL` and `e ∈ CE ∥ AL`, so `d` is on `b`'s side of `AL` and `e`
is on `c`'s side.  From the (already established) `between b l' c` with `l' ∈ AL`, `b` and
`c` are on opposite sides of `AL`; transitivity then puts `d`,`e` on opposite sides too,
and pasch_4 (AL meets DE at l) gives `between d l e`.

No angle hypotheses — pure side/betweenness transfer, so it holds in every configuration.
-/
theorem helper_47_between_dle :
    ∀ (a b c d e l l' : Point) (BC BD CE DE AL : Line),
    a.onLine AL ∧ ¬a.onLine BD ∧ ¬a.onLine CE ∧
    b.onLine BC ∧ c.onLine BC ∧
    b.onLine BD ∧ c.onLine CE ∧
    d.onLine BD ∧ e.onLine CE ∧
    d.onLine DE ∧ e.onLine DE ∧ d ≠ e ∧
    l.onLine AL ∧ l.onLine DE ∧
    l'.onLine AL ∧ l'.onLine BC ∧
    between b l' c ∧
    ¬AL.intersectsLine BD ∧ ¬AL.intersectsLine CE →
    between d l e :=
by
  euclid_intros
  -- AL is distinct from the two parallel square sides (else apex a would lie on them).
  have hALBD : AL ≠ BD := by euclid_finish
  have hALCE : AL ≠ CE := by euclid_finish
  -- b,c,d,e are all off AL (each lies on a line that only meets AL... not at all: parallel).
  have hbAL : ¬b.onLine AL := by
    by_contra
    euclid_apply (intersection_lines_common_point b AL BD)
    euclid_finish
  have hcAL : ¬c.onLine AL := by
    by_contra
    euclid_apply (intersection_lines_common_point c AL CE)
    euclid_finish
  have hdAL : ¬d.onLine AL := by
    by_contra
    euclid_apply (intersection_lines_common_point d AL BD)
    euclid_finish
  have heAL : ¬e.onLine AL := by
    by_contra
    euclid_apply (intersection_lines_common_point e AL CE)
    euclid_finish
  -- d,b on BD ∥ AL ⟹ same side of AL  (else segment d─b would cross AL, i.e. AL meets BD).
  have hdb : d.sameSide b AL := by
    by_contra
    euclid_apply (intersection_lines_opposing d b AL BD)
    euclid_finish
  -- e,c on CE ∥ AL ⟹ same side of AL.
  have hec : e.sameSide c AL := by
    by_contra
    euclid_apply (intersection_lines_opposing e c AL CE)
    euclid_finish
  -- between b l' c with l' on AL ⟹ b,c on opposite sides of AL.
  euclid_apply (pasch_3 b l' c AL)
  -- transitivity ⟹ d,e opposite across AL.
  have hde : ¬d.sameSide e AL := by euclid_finish
  -- AL meets DE at l, d≠e on DE, d,e opposite across AL ⟹ between d l e.
  euclid_apply (pasch_4 d l e AL DE)
  euclid_finish

/-
Helper for Prop47  `(∠ d:b:a : ℝ) = ∠ f:b:c`.
Square ABFG on AB (∠a:b:f = ∟, f off AB opposite c); square BCDE on BC (∠c:b:d = ∟,
d off BC opposite a).  Both ∠d:b:a and ∠f:b:c equal ∟ + ∠a:b:c.
d on BD (through b); f on BF (through b).
-/
theorem helper_47_angle_dba_eq_fbc :
    ∀ (a b c d f : Point) (AB BC AC BD BF : Line),
    -- triangle abc with the right angle at a (the governing Prop47 premise):
    a.onLine AB ∧ b.onLine AB ∧ a ≠ b ∧
    b.onLine BC ∧ c.onLine BC ∧ b ≠ c ∧
    a.onLine AC ∧ c.onLine AC ∧ a ≠ c ∧
    AB ≠ BC ∧ BC ≠ AC ∧ AC ≠ AB ∧
    (∠ b:a:c : ℝ) = ∟ ∧
    ¬c.onLine AB ∧ ¬a.onLine BC ∧
    ¬f.onLine AB ∧ ¬d.onLine BC ∧
    ¬f.sameSide c AB ∧
    ¬d.sameSide a BC ∧
    -- construction data Prop47 has (this✝² @ line 69) but the trimmed context can't re-derive:
    d.sameSide c AB ∧
    b.onLine BD ∧ d.onLine BD ∧
    b.onLine BF ∧ f.onLine BF ∧
    (∠ a:b:f : ℝ) = ∟ ∧
    (∠ c:b:d : ℝ) = ∟ →
    (∠ d:b:a : ℝ) = (∠ f:b:c : ℝ) :=
by
  euclid_intros
  -- (1) acuteness at b, from prop17 + right angle at a (mirrors Prop47:26-28)
  euclid_apply (proposition_17 c a b AC AB BC)
  have hAcuteB : (∠ a:b:c : ℝ) < ∟ := by euclid_finish
  -- (2) acuteness at c, symmetric (mirrors Prop47:44-46)
  euclid_apply (proposition_17 b c a BC AC AB)
  have hAcuteC : (∠ a:c:b : ℝ) < ∟ := by euclid_finish
  -- (3) the four sameSide preconditions of the two splits.
  --   hA11, hC11 (orig point vs square side): derivable & fast.
  --   hA10, hC10 (square corner vs orig line): NOT derivable from this context (construction data).
  have hA11 : a.sameSide c BD := by euclid_finish
  have hC11 : c.sameSide a BF := by
    euclid_apply (helper_47_sameSide_perp c a b f AB BF)
    euclid_finish
  have hA10 : d.sameSide c AB := by euclid_finish
  -- hC10 from triple_incidence_2 (lines BF,AB,BC at b): consumes hC11 (a.sameSide c BF),
  -- ¬f.sameSide c AB, ¬c.onLine AB, f≠b ⟹ f.sameSide a BC.  No circularity.
  have hC10 : f.sameSide a BC := by
    euclid_apply (triple_incidence_2 BF AB BC b f a c)
    euclid_finish
  -- (4) the two splits + arithmetic
  euclid_apply sum_angles_onlyif b d a c BD AB
  euclid_apply sum_angles_onlyif b f c a BF BC
  euclid_finish

-- WARNING: This proof is quite slow.
set_option maxHeartbeats 0 in
theorem proposition_47 : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| :=
by
  euclid_intros
  euclid_apply (proposition_46' b a c AB) as (f, g, FG, BF, AG)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)

  -- Missed by Euclid.
  have : (∠ a:b:c : ℝ) < ∟ := by
    euclid_apply (proposition_17 c a b AC AB BC)
    euclid_finish

  -- Missed by Euclid.
  have : ¬(d.onLine AB) := by
    by_contra
    euclid_apply (proposition_13 c b a d BC AB)
    euclid_finish

  -- Missed by Euclid.
  have : (d.sameSide c AB) := by
    euclid_apply (extend_point AB a b) as b'
    euclid_apply (proposition_16 c a b b' AC AB BC)
    euclid_assert (∠ c:b:b' : ℝ) > ∟
    euclid_finish

  -- Missed by Euclid.
  have : (∠ a:c:b : ℝ) < ∟ := by
    euclid_apply (proposition_17 b c a BC AC AB)
    euclid_finish

  -- Missed by Euclid.
  have : ¬(e.onLine AC) := by
    by_contra
    euclid_apply (proposition_13 b c a e BC AC)
    euclid_finish

  -- Missed by Euclid.
  have : (e.sameSide b AC) := by
    euclid_apply (extend_point AC a c) as c'
    euclid_apply (proposition_16 b a c c' AB AC BC)
    euclid_assert (∠ b:c:c' : ℝ) > ∟
    euclid_apply (helper_47_e_sameSide_b_AC a b c d e c' AB BC AC BD CE DE)
    euclid_finish

  euclid_apply (proposition_31 a b d BD) as AL
  euclid_apply (proposition_30 AL CE BD)
  euclid_apply (intersection_lines AL DE) as l
  euclid_apply (intersection_lines AL BC) as l'
  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_14 b a c g AB AC AG)
  euclid_apply (proposition_14 c a b h AC AB AH)
  euclid_apply (helper_47_angle_dba_eq_fbc a b c d f AB BC AC BD BF)
  euclid_assert ((∠ d:b:a : ℝ) = ∠ f:b:c)
  euclid_assert ((∠ c:b:a : ℝ) + ∟ = ∠ c:b:f)
  euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
  euclid_assert ((Triangle.area △ a:b:d) = Triangle.area △ b:c:f)
  euclid_apply (proposition_41 l' b d l a AL BD BC DE AB AD)
  euclid_apply (proposition_41 g f b a c AG BF FG AB FC BC)
  euclid_assert ((Triangle.area △ g:f:b : ℝ) + (Triangle.area △ g:b:a) = (Triangle.area △ l':b:d) + (Triangle.area △ l':d:l))
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b k) as BK
  euclid_apply sum_angles_onlyif c e a b CE AC
  euclid_apply sum_angles_onlyif c k b a CK BC
  euclid_assert ((∠ e:c:a : ℝ) = (∠ k:c:b))
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_assert ((Triangle.area △ a:c:e : ℝ) = Triangle.area △ c:b:k)
  euclid_apply (proposition_41 l' c e l a AL CE BC DE AC AE)
  euclid_apply (proposition_41 h k c a b AH CK HK AC BK BC)
  euclid_assert ((Triangle.area △ k:c:a : ℝ) + (Triangle.area △ k:a:h) = (Triangle.area △ l':c:e) + (Triangle.area △ l':e:l))
  euclid_apply (rectangle_area b c d e BC DE BD CE)
  euclid_apply (rectangle_area b a f g AB FG BF AG)
  euclid_apply (rectangle_area a c h k AC HK AH CK)
  -- AL ⊥ BC at the foot l' (AL ∥ BD ⊥ BC, and AL ∥ CE ⊥ BC), needed by between_blc.
  -- a is off the square sides BD, CE: else a ∈ AL ∩ BD (resp. CE) would force AL to meet
  -- the parallel BD (resp. CE) — proven explicitly, no SMT search.
  have haBD : ¬(a.onLine BD) := by
    by_contra
    euclid_apply (intersection_lines_common_point a AL BD)
    euclid_finish
  have haCE : ¬(a.onLine CE) := by
    by_contra
    euclid_apply (intersection_lines_common_point a AL CE)
    euclid_finish
  euclid_apply (helper_47_AL_perp_BC a b c d l' BC BD AL)
  euclid_apply (helper_47_AL_perp_BC a c b e l' BC CE AL)
  euclid_apply (helper_47_between_blc a b c l' AB BC AC BD CE AL)
  euclid_apply (helper_47_between_dle a b c d e l l' BC BD CE DE AL)
  euclid_apply sum_parallelograms_area b c d e l' l BC DE BD CE
  euclid_apply parallelogram_area b l' d l BC DE BD AL
  euclid_assert ((Triangle.area △ b:d:e : ℝ) + (Triangle.area △ b:e:c) = (Triangle.area △ g:f:b) + (Triangle.area △ g:b:a) + (Triangle.area △ k:c:a) + (Triangle.area △ k:a:h))
  euclid_finish

end Elements.Book1
