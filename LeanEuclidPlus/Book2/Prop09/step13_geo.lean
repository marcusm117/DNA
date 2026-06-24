import SystemE
import Book2.Prop09.step13_gef
import Book2.Prop09.step13_formtri
import Book2.Prop09.step13_sum
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step13 geometry (no ∟/2), container: ∠g:e:f = ∠c:e:b (step13_gef), formTriangle EGF
-- (step13_formtri), and the angle-sum (step13_sum, using ∠e:g:f = ∟).
theorem helper_2_9_step13_geo
  (a b c d e f g e0 e1 : Point) (AB CE DF EB FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB) (hab_d : d.onLine AB)
  (hcdb : between c d b)
  (hdf_d : d.onLine DF) (hdf_f : f.onLine DF)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hpar_df : ¬DF.intersectsLine CE)
  (hbegc : between e g c)
  (hbefb : between e f b)
  (hegf : ∠ e:g:f = ∟) :
  (∠ g:e:f = ∠ c:e:b) ∧ (∠ g:e:f + ∠ e:f:g = ∟) := by
  have step13_gef : ∠ g:e:f = ∠ c:e:b := by euclid_apply (helper_2_9_step13_gef a b c e f g e0 e1 AB CE EB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_formtri : formTriangle e g f CE FG EB := by euclid_apply (helper_2_9_step13_formtri a b c d e f g e0 e1 AB CE DF EB FG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_sum : ∠ g:e:f + ∠ e:f:g = ∟ := by euclid_apply (helper_2_9_step13_sum a b c e f g AB CE EB FG (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  exact ⟨step13_gef, step13_sum⟩

end Elements.Book2
