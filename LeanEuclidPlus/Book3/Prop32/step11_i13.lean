import SystemE
import Book1.Prop13.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Obtuse-case duality (I.13): the straight-line EF makes ∠f:b:d + ∠e:b:d = two right-angles.
theorem helper_3_32_step11_i13 (b d e f : Point) (BD EF : Line)
    (h_d_BD : d.onLine BD) (h_b_BD : b.onLine BD) (h_bd : b ≠ d)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ebf : between e b f)
    (h_f_offBD : ¬f.onLine BD) :
    ∠ f:b:d + ∠ e:b:d = ∟ + ∟ := by
  euclid_apply (Elements.Book1.proposition_13 d b f e BD EF)
  euclid_finish

end Elements.Book3
