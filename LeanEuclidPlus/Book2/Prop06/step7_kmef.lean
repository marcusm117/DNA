import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.7 sub: KM ∥ EF. KM ∥ AB and AB ∥ EF, so KM ∥ EF [Prop.~1.30]. The pairwise-distinctness is
   derived in-body from off-line anchors: KM ≠ AB (h ∈ KM, ¬h ∈ AB), EF ≠ AB (e ∈ EF, ¬e ∈ AB),
   KM ≠ EF (h ∈ KM, ¬h ∈ EF). -/
theorem helper_2_6_step7_kmef (e h : Point) (AB KM EF : Line)
    (heEF : e.onLine EF) (hhKM : h.onLine KM)
    (hhoffAB : ¬(h.onLine AB)) (heoffAB : ¬(e.onLine AB)) (hhoffEF : ¬(h.onLine EF))
    (hKMAB : ¬(KM.intersectsLine AB)) (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(KM.intersectsLine EF) := by
  euclid_intros
  have hKMneAB : KM ≠ AB := fun heq => hhoffAB (heq ▸ hhKM)
  have hEFneAB : EF ≠ AB := fun heq => heoffAB (heq ▸ heEF)
  have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
  euclid_apply (proposition_30 KM EF AB)
  euclid_finish

end Elements.Book2
