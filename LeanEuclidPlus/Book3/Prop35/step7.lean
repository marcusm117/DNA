import SystemE
import Book2.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- II.5 applied to AC cut equally at the midpoint G and (unequally) at E. Euclid's diagram fixes the
-- order A,G,E,C; that order is not forced (E can be either side of G, or coincide with it), so we
-- fix it here with a by_cases and apply II.5 [Prop.~2.5] in each non-degenerate branch.
theorem helper_3_35_step7 (a c e g : Point) (AC : Line)
  (hbet_aec : between a e c) (haAC : a.onLine AC) (hcAC : c.onLine AC) (hgAC : g.onLine AC)
  (hassump1 : |(a─g)| = |(g─c)|)   -- @assumption
  : |(a─e)| * |(e─c)| + |(e─g)| * |(e─g)| = |(g─c)| * |(g─c)| := by
  by_cases heg : e = g
  · subst heg
    euclid_finish
  · by_cases hord : between a g e
    · -- order A, G, E, C
      euclid_apply (Elements.Book2.proposition_5 a c g e AC)
      euclid_finish
    · -- order A, E, G, C
      euclid_apply (Elements.Book2.proposition_5 c a g e AC)
      euclid_finish

end Elements.Book3
