import SystemE

namespace Elements.Book1

/-
Helper for Prop47.lean:89  precondition `between d l e` of `sum_parallelograms_area`.

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

end Elements.Book1