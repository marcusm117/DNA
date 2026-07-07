import SystemE
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_1_step11 (a b d g : Point) (AB GA GD GB : Line)
    (h_a_on_AB : a.onLine AB) (h_b_on_AB : b.onLine AB)
    (h_g_on_GA : g.onLine GA) (h_a_on_GA : a.onLine GA)
    (h_g_on_GD : g.onLine GD) (h_d_on_GD : d.onLine GD)
    (h_g_on_GB : g.onLine GB) (h_b_on_GB : b.onLine GB)
    (h_bet_adb : between a d b)
    (h_gNa : g ≠ a) (h_gNd : g ≠ d) (h_gNb : g ≠ b)
    (h_step9 : |(a─d)| = |(b─d)| ∧ |(d─g)| = |(d─g)|)
    (h_ga_gb : |(g─a)| = |(g─b)|) :
    ∠ a:d:g = ∠ g:d:b := by
  have h_ad_db := h_step9.1
  have h_d_on_AB : d.onLine AB := between_same_line_in a d b AB ⟨h_bet_adb, h_a_on_AB, h_b_on_AB⟩
  have h_dNa : d ≠ a := Ne.symm (between_symm a d b h_bet_adb).2.1
  have h_dNb : d ≠ b := Ne.symm (between_symm b d a (between_symm a d b h_bet_adb).1).2.1
  have h_form1 : formTriangle d a g AB GA GD := by euclid_finish
  have h_form2 : formTriangle d b g AB GB GD := by euclid_finish
  have h_da_db : |(d─a)| = |(d─b)| := by euclid_finish
  have h_ag_bg : |(a─g)| = |(b─g)| := by euclid_finish
  have h8 : ∠ a:d:g = ∠ b:d:g := by
    euclid_apply (proposition_8 d a g d b g AB GA GD AB GB GD ⟨h_form1, h_form2, h_da_db, rfl, h_ag_bg⟩)
  euclid_finish

end Elements.Book3
