import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_12_step1_fcd (f g c d : Point) (FG : Line)
    (hfcg : between f c g)
    (hgdc : between g d c)
    (hcdg : between c d g)
    (hf_FG : f.onLine FG) (hc_FG : c.onLine FG) (hd_FG : d.onLine FG)
    : between f c d := by
  have hgcf : between g c f := (between_symm f c g hfcg).1
  have hgdf : between g d f := between_trans_in g c f d ⟨hgcf, hgdc⟩
  have hfdg : between f d g := (between_symm g d f hgdf).1
  have hfNc : f ≠ c := by euclid_finish
  have hcNd : c ≠ d := by euclid_finish
  have hdNf : d ≠ f := by euclid_finish
  rcases between_points f c d FG ⟨hfNc, hcNd, hdNf, hf_FG, hc_FG, hd_FG⟩
      with h1 | h2 | h3
  · exact h1
  · -- between c f d contradicts between f c g via lengths: gives 2|f─c| = 0
    have hlen_h2 := between_if c f d h2
    have hlen_fcg := between_if f c g hfcg
    have hlen_cdg := between_if c d g hcdg
    have hlen_fdg := between_if f d g hfdg
    have hfcNz : |(f─c)| ≠ 0 := fun h => hfNc (zero_segment_if f c h)
    have hfc_pos : 0 < |(f─c)| :=
      lt_of_le_of_ne (segment_gte_zero (f─c)) (Ne.symm hfcNz)
    linarith [segment_symmetric c f]
  · -- between f d c contradicts between c d g via between_not_trans
    exact absurd hcdg (between_not_trans f d c g ⟨h3, hfdg⟩)

end Elements.Book3
