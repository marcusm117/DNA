import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_11_step6
    (a f h g : Point) (AC GH AH FG : Line)
    (hgf : g ≠ f)
    (haAC : a.onLine AC) (hfAC : f.onLine AC)
    (hhGH : h.onLine GH) (hgGH : g.onLine GH)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hgFG : g.onLine FG) (hfFG : f.onLine FG)
    (hsameSide : h.sameSide a FG)
    (hpar1 : ¬GH.intersectsLine AC) (hpar2 : ¬AH.intersectsLine FG)
    (hhg : |(h─g)| = |(a─f)|) (hah : |(a─h)| = |(a─f)|)
    (hfg : |(f─g)| = |(a─f)|)
    (hang1 : ∠ f:a:h = ∟) (hang2 : ∠ a:h:g = ∟)
    (hang3 : ∠ a:f:g = ∟) (hang4 : ∠ f:g:h = ∟) :
    formParallelogram h g a f GH AC AH FG ∧ |(h─g)| = |(a─f)| ∧ |(a─h)| = |(a─f)| ∧ |(f─g)| = |(a─f)| ∧ ∠ f:a:h = ∟ ∧ ∠ a:f:g = ∟ ∧ ∠ a:h:g = ∟ ∧ ∠ f:g:h = ∟ := by
  euclid_finish

end Elements.Book2
