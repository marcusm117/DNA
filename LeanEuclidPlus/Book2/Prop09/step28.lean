import SystemE
import Book.Prop34
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1 Elements

set_option systemE.solverTime 30 in
theorem helper_2_9_step28
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
  (hpar_fg : ¬FG.intersectsLine AB) :
  |(g─f)| = |(c─d)| := by
  have step28_pgram : formParallelogram g f c d FG AB CE DF := by sorry
  euclid_apply (line_from_points f c) as FC
  euclid_apply (proposition_34 g f c d FG AB CE DF FC)
  euclid_finish

end Elements.Book2
