import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15 sub (generic): p.sameSide q DG for two points p,q on CE. CE ∥ DG (¬DG∩CE, DG ≠ CE since
   d ∉ CE wait — d ∈ DG, d ∉ CE), so p,q (both on CE) are off DG and cannot be opposite. Reused for
   (l,e) and (l,c). -/
theorem helper_2_5_step15_ssce (d p q : Point) (CE DG : Line)
    (hpCE : p.onLine CE) (hqCE : q.onLine CE)
    (hdDG : d.onLine DG)
    (hpq : p ≠ q)
    (hDGCE : ¬(DG.intersectsLine CE))
    (hpoffDG : ¬(p.onLine DG)) :
    p.sameSide q DG := by
  euclid_intros
  have hqoffDG : ¬(q.onLine DG) := by
    intro hon; euclid_apply (intersection_lines_common_point q DG CE); euclid_finish
  have hDGneCE : DG ≠ CE := fun heq => hpoffDG (heq ▸ hpCE)
  by_contra hns
  euclid_apply (intersection_lines_opposing p q DG CE)
  euclid_finish

end Elements.Book2
