import SystemE
import Book3.Prop12.step1_cNotIn
import Book3.Prop12.step1_cNotOn
import Book3.Prop12.step1_fcd
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step1 (a f g : Point) (ABC ADE : Circle)
    (left : f.isCentre ABC)
    (left_1 : g.isCentre ADE)
    (left_2 : a.onCircle ABC)
    (left_3 : a.onCircle ADE)
    (left_4 : ¬ABC.intersectsCircle ADE)
    (hfNotIn : ¬f.insideCircle ADE) (hfNotOn : ¬f.onCircle ADE)
    (left_6 : ¬g.insideCircle ABC) (right_6 : ¬g.onCircle ABC)
    (hsuppose1 : ¬between f a g)
    : ∃ (c d : Point), c.onCircle ABC ∧ d.onCircle ADE ∧ between f c d ∧ between c d g := by
  have hf_in : f.insideCircle ABC := center_inside_circle f ABC left
  have hg_in : g.insideCircle ADE := center_inside_circle g ADE left_1
  have hfNg : f ≠ g := fun heq => left_6 (heq ▸ hf_in)
  obtain ⟨FG, hf_FG, hg_FG⟩ := line_from_points f g hfNg
  obtain ⟨c, hc_ABC, hc_FG, hfcg⟩ :=
    intersection_circle_line_between_points ABC FG f g
      ⟨hf_in, hf_FG, ⟨left_6, right_6⟩, hg_FG⟩
  have step1_cNotIn : ¬c.insideCircle ADE := by euclid_apply (helper_3_12_step1_cNotIn c f ABC ADE (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.insideCircle ABC; assumption)) (by euclid_assumption "" (show ¬ABC.intersectsCircle ADE; assumption)) (by euclid_assumption "" (show ¬f.insideCircle ADE; assumption)) (by euclid_assumption "" (show ¬f.onCircle ADE; assumption)))
  have step1_cNotOn : ¬c.onCircle ADE := by euclid_apply (helper_3_12_step1_cNotOn a f g c ABC ADE FG (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show ¬between f a g; assumption)) (by euclid_assumption "" (show f.insideCircle ABC; assumption)) (by euclid_assumption "" (show g.insideCircle ADE; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onLine FG; assumption)) (by euclid_assumption "" (show between f c g; assumption)) (by euclid_assumption "" (show ¬c.insideCircle ADE; assumption)))
  obtain ⟨d, hd_ADE, hd_FG, hgdc⟩ :=
    intersection_circle_line_between_points ADE FG g c
      ⟨hg_in, hg_FG, ⟨step1_cNotIn, step1_cNotOn⟩, hc_FG⟩
  have hcdg : between c d g := (between_symm g d c hgdc).1
  have step1_fcd : between f c d := by euclid_apply (helper_3_12_step1_fcd f g c d FG (by euclid_assumption "" (show between f c g; assumption)) (by euclid_assumption "" (show between g d c; assumption)) (by euclid_assumption "" (show between c d g; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show c.onLine FG; assumption)) (by euclid_assumption "" (show d.onLine FG; assumption)))
  exact ⟨c, d, hc_ABC, hd_ADE, step1_fcd, hcdg⟩

end Elements.Book3
