import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_9_step4 (d e f : Point) (DE EF DF : Line)
    (h1 : d.onLine DE) (h2 : e.onLine DE) (h3 : d ≠ e)
    (h4 : e.onLine EF) (h5 : f.onLine EF)
    (h6 : d.onLine DF) (h7 : f.onLine DF)
    (h8 : ¬f.onLine DE)
    (h9 : |(f─d)| = |(d─e)|) (h10 : |(f─e)| = |(d─e)|) :
    formTriangle d e f DE EF DF ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)| := by
  refine ⟨?_, h9, h10⟩
  refine ⟨⟨h1, h2, h3⟩, h4, h5, h7, h6, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
