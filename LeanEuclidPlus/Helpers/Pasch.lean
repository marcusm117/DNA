import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements

/- Shared Pasch/betweenness wrappers. These are THIN curried forms of the `pasch_2/3/4` axioms:
   the axioms already do the geometric work; the wrappers just take the preconditions as separate
   ATOMIC hyps (so `(by assumption)` discharges them positionally) and return the single conclusion,
   collapsing each recurring call site to one `euclid_apply`. The genuinely hard, figure-specific
   glue — deriving the `¬sameSide` / off-line preconditions — stays INLINE at the call site (it is
   not generalizable), exactly as with the OffLine/SameSide helpers.

   Lifted verbatim from the building proofs: pasch_2 ← Book2/Prop09 step13_fsb; pasch_4 ← Book/Prop44
   `helper_44_between_*`; pasch_3 ← Book/Prop24, Book/Prop47. -/

/- pasch_2: `a` on `L`, `b` off `L`, and `a` between `b`'s pair `between a b c` ⟹ `b`,`c` same side of `L`.
   (`a.onLine L` + `¬(b.onLine L)` + `between a b c` ⟹ `b.sameSide c L`.) -/
theorem sameSide_of_between (a b c : Point) (L : Line)
    (haL : a.onLine L) (hbL : ¬(b.onLine L)) (hbet : between a b c) :
    b.sameSide c L := by
  euclid_apply (pasch_2 a b c L)
  euclid_finish

/- pasch_3: `b` on `L` and `between a b c` ⟹ `a` and `c` are on OPPOSITE sides of `L`
   (`¬(a.sameSide c L)`). -/
theorem not_sameSide_of_between (a b c : Point) (L : Line)
    (hbL : b.onLine L) (hbet : between a b c) :
    ¬(a.sameSide c L) := by
  euclid_apply (pasch_3 a b c L)
  euclid_finish

/- pasch_4: the converse-assembly. `b` is the crossing point (on both `L` and `M`), `a` and `c` lie on
   the second line `M` (distinct from each other and from `b`), `L ≠ M`, and `a`,`c` are on OPPOSITE
   sides of `L` (`¬(a.sameSide c L)`). Then `b` lies BETWEEN `a` and `c`. Atomic incidence hyps; the
   `distinctPointsOnLine a c M` the axiom wants is assembled by the solver from `haM`/`hcM`/`hac`. -/
theorem between_of_not_sameSide (a b c : Point) (L M : Line)
    (hLM : L ≠ M) (hbL : b.onLine L) (hbM : b.onLine M)
    (haM : a.onLine M) (hcM : c.onLine M)
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c)
    (hns : ¬(a.sameSide c L)) : between a b c := by
  euclid_apply (pasch_4 a b c L M)
  euclid_finish

end Elements
