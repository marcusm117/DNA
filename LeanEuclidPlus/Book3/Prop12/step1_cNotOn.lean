import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step1_cNotOn (a f g c : Point) (ABC ADE : Circle) (FG : Line)
    (left : f.isCentre ABC)
    (left_1 : g.isCentre ADE)
    (left_2 : a.onCircle ABC)
    (left_3 : a.onCircle ADE)
    (hsuppose1 : ¬between f a g)
    (hf_in : f.insideCircle ABC)
    (hg_in : g.insideCircle ADE)
    (hfNg : f ≠ g)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hc_ABC : c.onCircle ABC)
    (hc_FG : c.onLine FG)
    (hfcg : between f c g)
    (step1_cNotIn : ¬c.insideCircle ADE)
    : ¬c.onCircle ADE := by
  intro hc_on
  have hgc_ga : |(g─c)| = |(g─a)| := by
    euclid_apply (point_on_circle_onlyif g a c ADE)
    euclid_finish
  have hfc_fa : |(f─c)| = |(f─a)| := by
    euclid_apply (point_on_circle_onlyif f a c ABC)
    euclid_finish
  have hbet_fcg : |(f─c)| + |(c─g)| = |(f─g)| := between_if f c g hfcg
  have hsum : |(f─a)| + |(g─a)| = |(f─g)| := by
    linarith [segment_symmetric c g]
  have hfNa : f ≠ a := fun h => inside_not_on_circle f ABC hf_in (h ▸ left_2)
  have hgNa : g ≠ a := fun h => inside_not_on_circle g ADE hg_in (h ▸ left_3)
  rcases Classical.em (a.onLine FG) with ha_FG | ha_not_FG
  · rcases between_points f g a FG ⟨hfNg, hgNa, hfNa.symm, hf_FG, hg_FG, ha_FG⟩
        with h1 | h2 | h3
    · have hlen := between_if f g a h1
      have hga_zero : |(g─a)| = 0 := by linarith [segment_symmetric g a, segment_symmetric f g]
      exact hgNa (zero_segment_if g a hga_zero)
    · have hlen := between_if g f a h2
      have hfa_zero : |(f─a)| = 0 := by linarith [segment_symmetric g f, segment_symmetric f a]
      exact hfNa (zero_segment_if f a hfa_zero)
    · exact hsuppose1 h3
  · obtain ⟨AF, ha_AF, hf_AF⟩ := line_from_points a f hfNa.symm
    obtain ⟨AG, ha_AG, hg_AG⟩ := line_from_points a g hgNa.symm
    have hAFneFG : AF ≠ FG := by euclid_finish
    have hFGneAG : FG ≠ AG := by euclid_finish
    have hAGneAF : AG ≠ AF := by euclid_finish
    have hform : formTriangle a f g AF FG AG :=
      ⟨⟨ha_AF, hf_AF, hfNa.symm⟩, hf_FG, hg_FG, hg_AG, ha_AG,
       hAFneFG, hFGneAG, hAGneAF⟩
    have h20 := Elements.Book1.proposition_20 a f g AF FG AG hform
    linarith [segment_symmetric a g]

end Elements.Book3
