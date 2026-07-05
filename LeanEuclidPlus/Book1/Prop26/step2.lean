import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step2
    (b g a d e c : Point) (GC : Line)
    (hbetween : between b g a)
    (hlen : |(b─g)| = |(e─d)|)
    (hg_GC : g.onLine GC)
    (hc_GC : c.onLine GC) :
    between b g a ∧ |(b─g)| = |(d─e)| ∧ g.onLine GC ∧ c.onLine GC := by
  exact ⟨hbetween, by euclid_finish, hg_GC, hc_GC⟩

end Elements.Book1
