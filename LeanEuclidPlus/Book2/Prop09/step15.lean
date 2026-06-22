import SystemE
import Book.Prop06
import Helpers.OffLine
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

set_option systemE.solverTime 30 in
-- step15 (2.9.15): |EG| = |GF| (proposition_6 on △EGF). ∠g:e:f = ∠e:f:g (step14) and
-- angle_symm give ∠g:e:f = ∠g:f:e; formTriangle g e f + prop_6 ⟹ |g─e| = |g─f|.
-- between e g c (from step13_egc) gives e≠g for the off-line facts.
theorem helper_2_9_step15
  (a b c d e f g e0 e1 : Point) (AB CE EB DF FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hpar_df : ¬DF.intersectsLine CE)
  (hpar_fg : ¬FG.intersectsLine AB)
  (h14 : ∠ g:e:f = ∠ e:f:g) :
  |(e─g)| = |(g─f)| := by
  have step13_befb : between e f b := by sorry
  have step13_egc : between e g c := by sorry
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hdoffCE : ¬(d.onLine CE) :=
    offLine_of_two_points d c e0 AB CE hab_d hab_c (by euclid_finish) hce_c hce_e0 hne0
  have hDFneCE : DF ≠ CE := fun h => hdoffCE (h ▸ hdf_d)
  have hfoffCE : ¬(f.onLine CE) :=
    offLine_of_parallel_simple f DF CE hdf_f hDFneCE hpar_df
  have heg : e ≠ g := by euclid_finish
  have heoffFG : ¬(e.onLine FG) :=
    offLine_of_two_points e g f CE FG heCE hce_g heg hfg_g hfg_f hfoffCE
  have hCEneEB : CE ≠ EB := fun h => hfoffCE (h ▸ heb_f)
  have hFGneCE : FG ≠ CE := fun h => hfoffCE (h ▸ hfg_f)
  have hEBneFG : EB ≠ FG := fun h => heoffFG (h ▸ heb_e)
  have hformTri : formTriangle g e f CE EB FG := by euclid_finish
  have hef : e ≠ f := by euclid_finish
  have hfg : f ≠ g := by euclid_finish
  have hsymm : ∠ e:f:g = ∠ g:f:e := angle_symm e f g ⟨hef, hfg⟩
  have hbase : ∠ g:e:f = ∠ g:f:e := by linarith
  euclid_apply (proposition_6 g e f CE EB FG)
  euclid_finish

end Elements.Book2
