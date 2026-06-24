import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
theorem helper_2_9_step17_symm
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
  (hbefb : between e f b) :
  ∠ d:f:b = ∠ b:f:d := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  have hec : e ≠ c := by euclid_finish
  have haoffCE : ¬(a.onLine CE) :=
    offLine_of_two_points a c e0 AB CE hab_a hab_c (by euclid_finish) hce_c hce_e0 hne0
  have heoffAB : ¬(e.onLine AB) :=
    offLine_of_two_points e c a CE AB heCE hce_c hec hab_c hab_a haoffCE
  have hfb : f ≠ b := by euclid_finish
  have hfoffAB : ¬(f.onLine AB) :=
    offLine_of_two_points' f b e EB AB heb_f heb_b hfb hab_b heb_e heoffAB
  have hdf : d ≠ f := fun h => hfoffAB (h ▸ hab_d)
  exact angle_symm d f b ⟨hdf, hfb⟩

end Elements.Book2
