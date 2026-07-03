import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
open Classical

namespace Elements.Book1

theorem helper_1_4_step1
  (a b c d e : Point) (b' c' : Point) (DE : Line)
  (right_3 : a ≠ b)
  (h_ab_db' : |(a─b)| = |(d─b')|)
  (h_b'_on_DE : b'.onLine DE)
  (h_not_between : ¬between b' d e)
  (h_d_on_DE : d.onLine DE)
  (h_e_on_DE : e.onLine DE)
  (h_d_ne_e : d ≠ e)
  (hassump1 : |(a─b)| = |(d─e)|)
  : (fun p : Point => if p = a then d else if p = b then b' else if p = c then c' else p) b = e := by
  simp only [if_neg (Ne.symm right_3), if_pos rfl]
  euclid_finish

end Elements.Book1
