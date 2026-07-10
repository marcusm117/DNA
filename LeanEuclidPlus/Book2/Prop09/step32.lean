import SystemE
import Book1.Prop47.Main
import Helpers.OffLine
import Mathlib.Tactic.Linarith
import Book2.Prop09.step13_befb
import Book2.Prop09.step32_formtri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

theorem helper_2_9_step32
  (a b c d e f e0 e1 : Point) (AB CE EA EB DF AF FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hea_e : e.onLine EA) (hea_a : a.onLine EA)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (haf_a : a.onLine AF) (haf_f : f.onLine AF)
  (hfg_f : f.onLine FG)
  (hpar_df : ¬DF.intersectsLine CE)
  (hpar_fg : ¬FG.intersectsLine AB)
  (hstep12 : ∠ a:e:b = ∟) :
  |(a─f)| * |(a─f)| = |(e─a)| * |(e─a)| + |(e─f)| * |(e─f)| := by
  -- @args: b c d e e0 e1 f AB CE DF EB
  have step13_befb : between e f b := by euclid_apply (helper_2_9_step13_befb b c d e e0 e1 f AB CE DF EB (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine EB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AB; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show ¬DF.intersectsLine CE; assumption)))
  have step32_formtri : formTriangle e a f EA AF EB := by euclid_apply (helper_2_9_step32_formtri a b c e f e0 e1 AB CE EA EB AF FG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e0.onLine CE; assumption)) (by euclid_assumption "" (show e1.onLine CE; assumption)) (by euclid_assumption "" (show ¬e0.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between c e e1; assumption)) (by euclid_assumption "" (show e.onLine EA; assumption)) (by euclid_assumption "" (show a.onLine EA; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show f.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine AB; assumption)) (by euclid_assumption "" (show between e f b; assumption)))
  have haef : ∠ a:e:f = ∟ := by euclid_finish
  euclid_apply (proposition_47 e a f EA AF EB)
  euclid_finish

end Elements.Book2
