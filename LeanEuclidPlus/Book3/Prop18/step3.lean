import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_18_step3 (c f g : Point) (DE FG : Line)
    (h_fon_FG : f.onLine FG) (h_gon_FG : g.onLine FG)
    (h_gon_DE : g.onLine DE) (h_con_DE : c.onLine DE)
    (h_foff_DE : ¬f.onLine DE) (h_fne_c : f ≠ c)
    (hassump1 : ∠ f:g:c > ∠ f:c:g) :
    |(f─c)| > |(f─g)| := by
  have hgne_c : g ≠ c := by
    intro hgc
    rw [hgc] at hassump1
    exact lt_irrefl _ hassump1
  euclid_apply (line_from_points f c) as FC
  have hfne_g : f ≠ g := fun h => h_foff_DE (h ▸ h_gon_DE)
  have htri : formTriangle f g c FG DE FC := by euclid_finish
  euclid_apply (Elements.Book1.proposition_19 f g c FG DE FC)
  euclid_finish

end Elements.Book3
