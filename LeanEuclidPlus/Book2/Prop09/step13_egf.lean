import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

set_option systemE.solverTime 30 in
-- step13 right-angle leaf: ∠e:g:f = ∟. proposition_29'''' gives ∠e:g:f = ∠g:c:b with
-- between e g c + f.sameSide b CE supplied (no SMT search); ∠g:c:b = ∟ (hrcb) closes it.
theorem helper_2_9_step13_egf
  (a b c d e f g e0 e1 : Point) (AB CE EB DF FG : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (hfg_f : f.onLine FG) (hfg_g : g.onLine FG)
  (hpar_fg : ¬FG.intersectsLine AB)
  (hfsb : f.sameSide b CE)
  (hbegc : between e g c)
  (hrcb : ∠ g:c:b = ∟) :
  ∠ e:g:f = ∟ := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  euclid_apply (proposition_29'''' f b e g c FG AB CE)
  euclid_finish

end Elements.Book2
