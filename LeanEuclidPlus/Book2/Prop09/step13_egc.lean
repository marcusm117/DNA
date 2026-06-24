import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step13 betweenness: g (= FG ∩ CE) lies between e and c on CE. Chain:
--   between e f b → f≠b; e off AB; f off AB → FG≠AB → g≠c;
--   c,b sameSide FG (AB∥FG); e,b opposite FG (pasch_3); → e,c opposite FG;
--   pasch_4 e g c FG CE.
theorem helper_2_9_step13_egc
  (a b c e f g e0 e1 : Point) (AB CE EB FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hpar : ¬FG.intersectsLine AB)
  (hbefb : between e f b) :
  between e g c := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have hec : e ≠ c := by euclid_finish
  have heoAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c hec hab_c hab_a haoffCE
  have hfb : f ≠ b := by euclid_finish
  have hfoffAB : ¬(f.onLine AB) :=
    offLine_of_two_points' f b e EB AB heb_f heb_b hfb hab_b heb_e heoAB
  have hFGneAB : FG ≠ AB := fun h => hfoffAB (h ▸ hfg_f)
  have hgnc : g ≠ c := by
    intro h
    have hcFG : c.onLine FG := h ▸ hfg_g
    have : FG.intersectsLine AB := by
      euclid_apply (intersection_lines_common_point c FG AB)
      euclid_finish
    exact hpar this
  have hnABiFG : ¬AB.intersectsLine FG := fun h => hpar (intersection_symm AB FG h)
  have hcbFG : c.sameSide b FG :=
    sameSide_of_parallel_both c b AB FG hab_c hab_b hFGneAB.symm hnABiFG
  have hnebFG : ¬(e.sameSide b FG) := by
    euclid_apply (pasch_3 e f b FG)
    assumption
  have hnecFG : ¬(e.sameSide c FG) := by
    intro h
    apply hnebFG
    exact same_side_symm b e FG (same_side_trans c b e FG ⟨hcbFG, same_side_symm e c FG h⟩)
  euclid_apply (pasch_4 e g c FG CE)
  euclid_finish

end Elements.Book2
