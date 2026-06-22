import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

set_option systemE.solverTime 30 in
-- step17 (2.9.17): ∠FBD = ∠DFB. Reuses step16's geometry: ∠f:b:d = ∠e:b:c (= ∟/2 by
-- step11), ∠b:f:d = ∟/2 (step16), and ∠d:f:b = ∠b:f:d (symm) ⟹ equal (linarith).
theorem helper_2_9_step17
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
  (h11 : ∠ c:e:b = ∟ / 2 ∧ ∠ e:b:c = ∟ / 2)
  (h16 : ∠ f:d:b = ∟ ∧ ∠ b:f:d = ∟ / 2) :
  ∠ f:b:d = ∠ d:f:b := by
  have step13_befb : between e f b := by sorry
  have step16_fbd : ∠ f:b:d = ∠ e:b:c := by sorry
  have hdfb : d ≠ f := by euclid_finish
  have hfb : f ≠ b := by euclid_finish
  have hsymm : ∠ d:f:b = ∠ b:f:d := angle_symm d f b ⟨hdfb, hfb⟩
  linarith

end Elements.Book2
