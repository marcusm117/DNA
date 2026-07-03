import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_8_step5
  (d e f g : Point) (AB AC DE EF DF EG GF : Line)
  (lineImg : Line → Line)
  (h_lineImg_AB : lineImg AB = EG)
  (step3 : lineImg AB ≠ DE ∧ lineImg AC ≠ DF)
  (step4 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG ∧
           distinctPointsOnLine g f GF ∧ |(e─g)| = |(e─d)| ∧ |(g─f)| = |(f─d)|)
  (he_DE : e.onLine DE) (hd_DE : d.onLine DE) (hne_de : d ≠ e)
  (hss : g.sameSide d EF)
  : g ≠ d ∧ g.sameSide d EF := by
  have hEGDE : EG ≠ DE := by rw [← h_lineImg_AB]; exact step3.1
  obtain ⟨_, ⟨he_EG, hg_EG, hne_eg⟩, _⟩ := step4
  clear h_lineImg_AB step3 lineImg
  refine ⟨?_, hss⟩
  euclid_finish

end Elements.Book1
