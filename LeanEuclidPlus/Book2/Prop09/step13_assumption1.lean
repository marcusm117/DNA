import SystemE
import Helpers.SameSide
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step13_assumption1: ∠g:e:f = ∟/2.
-- Strategy: first prove ∠g:e:f = ∠c:e:b geometrically (no ∟/2 in context during euclid_finish),
-- then linarith with h11.1.
theorem helper_2_9_step13_assumption1
  (a b c d e f g e0 e1 : Point) (AB CE DF EB FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hacb : between a c b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_b : b.onLine EB) (heb_f : f.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hpar_df : ¬DF.intersectsLine CE)
  (hpar_fg : ¬FG.intersectsLine AB)
  (h11 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2) :
  ∠ g:e:f = ∟ / 2 := by
  -- First prove ∠g:e:f = ∠c:e:b without h11 in euclid_finish scope
  -- (∟/2 in context causes "Improper numeric" SMT error)
  have hgef_ceb : ∠ g:e:f = ∠ c:e:b := by
    clear h11
    have heCE : e.onLine CE := by
      euclid_apply (between_same_line_in c e e1 CE)
      assumption
    -- between e f b
    have hbefb : between e f b := by
      have hdoffCE : ¬(d.onLine CE) :=
        offLine_of_two_points d c e0 AB CE hab_d hab_c (by euclid_finish) hce_c hce_e0 hne0
      have hCEneDF : CE ≠ DF := fun h => hdoffCE (h ▸ hdf_d)
      have hnCEiDF : ¬CE.intersectsLine DF := fun h => hpar_df (intersection_symm CE DF h)
      have hecDF : e.sameSide c DF :=
        sameSide_of_parallel_both e c CE DF heCE hce_c hCEneDF hnCEiDF
      have hncbDF : ¬(c.sameSide b DF) := by
        euclid_apply (pasch_3 c d b DF)
        assumption
      have hnebDF : ¬(e.sameSide b DF) := by
        intro h
        apply hncbDF
        exact same_side_symm b c DF (same_side_trans e b c DF ⟨h, hecDF⟩)
      euclid_apply (pasch_4 e f b DF EB)
      euclid_finish
    -- between e g c
    have hbegc : between e g c := by
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
        exact hpar_fg this
      have hnABiFG : ¬AB.intersectsLine FG := fun h => hpar_fg (intersection_symm AB FG h)
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
    -- ∠g:e:f = ∠c:e:b by ray coincidence
    euclid_apply (equal_angles e g c f b CE EB)
    euclid_finish
  linarith [h11.1]

end Elements.Book2
