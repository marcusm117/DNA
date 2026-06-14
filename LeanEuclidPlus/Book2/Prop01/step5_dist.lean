import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.5: shared distinctness of the cut points on BC (b,d,e,c are in the order
   b-d-e-c, so pairwise distinct), plus g is on BF (between b g f') and off BC (BF meets BC only
   at b, since f on BF is off BC, so g≠b on BF is off BC). -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step5_dist (b c d e f f' g : Point) (BC BF : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hf'BF : f'.onLine BF) (hbgf' : between b g f') :
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧ e ≠ c ∧ g.onLine BF ∧ ¬(g.onLine BC) := by
  euclid_intros
  euclid_apply (between_same_line_in b g f' BF)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book2
