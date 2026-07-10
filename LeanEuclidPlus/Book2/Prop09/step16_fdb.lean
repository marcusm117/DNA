import SystemE
import Book1Variants.Prop29
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

-- step16 right-angle: ∠f:d:b = ∟ (DF⊥AB). proposition_29'''' with DF∥CE and AB the
-- transversal: ∠b:d:f = ∠d:c:g (f on DF, g on CE∩FG); f.sameSide g AB is cheap (FG∥AB);
-- ∠d:c:g = ∟ (CE⊥AB). The off-line chain gives FG≠AB.
theorem helper_2_9_step16_fdb
  (a b c d e f g e0 e1 : Point) (AB CE DF EB FG : Line)
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
  (hbefb : between e f b)
  (hbegc : between e g c)
  (hstep1 : ∠ a:c:e = ∟) :
  ∠ f:d:b = ∟ := by
  have hbdc : between b d c := by euclid_finish
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
  have hfsgAB : f.sameSide g AB :=
    sameSide_of_parallel_both f g FG AB hfg_f hfg_g hFGneAB hpar_fg
  have hdrcg : ∠ d:c:g = ∟ := by euclid_finish
  euclid_apply (proposition_29'''' f g b d c DF CE AB)
  euclid_finish

end Elements.Book2
