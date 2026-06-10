import SystemE

namespace Elements.Book2

-- 2.4.7: GK = KB. Transitivity: GK = CB (step6) = BC = CG (step5) = KB (step6).
set_option systemE.solverTime 30 in
theorem helper_2_step7 (b c g k : Point)
    (hstep5 : |(b─c)| = |(c─g)|)
    (hstep6 : |(c─b)| = |(g─k)| ∧ |(c─g)| = |(k─b)|) :
    |(g─k)| = |(k─b)| := by
  euclid_intros
  euclid_finish

end Elements.Book2
