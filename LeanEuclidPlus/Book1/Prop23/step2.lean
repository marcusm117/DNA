import SystemE
import Book1.Prop23.step2_hfoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_23_step2 (a b f g : Point) (AB FA FG : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hg_AB : g.onLine AB) (hg_notbetween : ¬between g a b)
    (ha_FA : a.onLine FA) (hf_FA : f.onLine FA)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (h_af : |(a─f)| = |(c─d)|) (h_ag : |(a─g)| = |(c─e)|) (h_fg : |(f─g)| = |(e─d)|)
    (h1 : |(d─c)| + |(c─e)| > |(d─e)|)
    (h2 : |(e─d)| + |(d─c)| > |(e─c)|)
    (h3 : |(c─e)| + |(e─d)| > |(c─d)|)
    : formTriangle a f g FA FG AB := by
  have step2_hfoff : ¬f.onLine AB := by euclid_apply (helper_1_23_step2_hfoff c d e a b f g AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show |(a─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show |(a─g)| = |(c─e)|; assumption)) (by euclid_assumption "" (show |(f─g)| = |(e─d)|; assumption)) (by euclid_assumption "" (show |(d─c)| + |(c─e)| > |(d─e)|; assumption)) (by euclid_assumption "" (show |(e─d)| + |(d─c)| > |(e─c)|; assumption)) (by euclid_assumption "" (show |(c─e)| + |(e─d)| > |(c─d)|; assumption)))
  euclid_finish

end Elements.Book1
