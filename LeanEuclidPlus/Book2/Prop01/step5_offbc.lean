import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.5: the feet h, l, k (on the bottom line GH) lie off BC. GH ∥ BC and GH ≠ BC
   (g on GH is off BC), so GH does not meet BC, hence no point of GH is on BC. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step5_offbc (g h k l : Point) (BC GH : Line)
    (hgGH : g.onLine GH) (hgoffBC : ¬(g.onLine BC)) (hGHBC : ¬(GH.intersectsLine BC))
    (hhGH : h.onLine GH) (hlGH : l.onLine GH) (hkGH : k.onLine GH) :
    ¬(h.onLine BC) ∧ ¬(l.onLine BC) ∧ ¬(k.onLine BC) := by
  euclid_intros
  refine ⟨?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book2
