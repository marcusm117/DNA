import SystemE
import Book1.Prop17.Main
import Book1.Prop19.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_18_step8
    (c f : Point) (ABC : Circle) (DE : Line)
    (h_con : c.onCircle ABC)
    (h_con_DE : c.onLine DE)
    (h_no_int : ¬DE.intersectsCircle ABC)
    (h_centre : f.isCentre ABC)
    (h_fne_c : f ≠ c) :
    ∀ (g' : Point), g'.onLine DE → g' ≠ c → ¬∠ c:g':f = ∟ := by
  have hfoff : ¬f.onLine DE := by
    intro hfon
    exact h_no_int (intersection_circle_line_2 f ABC DE
      ⟨center_inside_circle f ABC h_centre, hfon⟩)
  euclid_apply (line_from_points f c) as FC
  intro g' hg'on hg'ne h1
  have hg'ne_f : g' ≠ f := fun h => hfoff (h ▸ hg'on)
  euclid_apply (line_from_points f g') as FG'
  have h_fgc : ∠ f:g':c = ∟ := by euclid_finish
  have htri : formTriangle f g' c FG' DE FC := by euclid_finish
  euclid_apply (Elements.Book1.proposition_17 f g' c FG' DE FC)
  have h_acute : ∠ g':c:f < ∟ := by linarith
  have h_ineq : ∠ f:g':c > ∠ g':c:f := by linarith
  euclid_apply (Elements.Book1.proposition_19 f g' c FG' DE FC)
  have hless : |(f─g')| < |(f─c)| := by euclid_finish
  exact h_no_int (intersection_circle_line_2 g' ABC DE
    ⟨point_in_circle_if f c g' ABC ⟨h_centre, h_con, hless⟩, hg'on⟩)

end Elements.Book3
