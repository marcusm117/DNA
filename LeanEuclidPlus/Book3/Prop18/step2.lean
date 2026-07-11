import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_18_step2 (c f g d : Point) (DE FG : Line)
    (h_fon_FG : f.onLine FG) (h_gon_FG : g.onLine FG)
    (h_gon_DE : g.onLine DE) (h_con_DE : c.onLine DE)
    (h_foff_DE : ¬f.onLine DE) (h_fne_c : f ≠ c)
    (h_don_DE : d.onLine DE) (h_dne_c : d ≠ c)
    (h_suppose1 : ∠ f:c:d ≠ ∟)
    (h_perp_univ : ∀ (p : Point), p.onLine DE → p ≠ g → ∠ p:g:f = ∟)
    (hassump1 : ∠ f:g:c = ∟) :
    ∠ f:c:g < ∟ := by
  have hgne_c : g ≠ c := by
    intro hgc
    have hdne_g : d ≠ g := fun h => h_dne_c (h.trans hgc)
    have hperp : ∠ d:g:f = ∟ := h_perp_univ d h_don_DE hdne_g
    exact h_suppose1 (by rw [← hgc]; euclid_finish)
  euclid_apply (line_from_points f c) as FC
  have hfne_g : f ≠ g := fun h => h_foff_DE (h ▸ h_gon_DE)
  have htri : formTriangle f g c FG DE FC := by euclid_finish
  euclid_apply (Elements.Book1.proposition_17 f g c FG DE FC)
  euclid_finish

end Elements.Book3
