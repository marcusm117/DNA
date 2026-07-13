import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step15 (f b : Point) (ABC : Circle) (FB : Line)
    (h_cen : f.isCentre ABC) (h_b_circ : b.onCircle ABC)
    (h_f_FB : f.onLine FB) (h_b_FB : b.onLine FB) (h_fb : f ≠ b) :
    ∃ g : Point, f.isCentre ABC ∧ between g f b ∧ g.onCircle ABC ∧ b.onCircle ABC := by
  have hf_in : f.insideCircle ABC := center_inside_circle f ABC h_cen
  obtain ⟨g, hg_circ, hg_FB, hbet⟩ :=
    intersection_circle_line_extending_points ABC FB f b ⟨hf_in, h_f_FB, h_b_FB, h_fb⟩
  exact ⟨g, h_cen, hbet, hg_circ, h_b_circ⟩

end Elements.Book3
