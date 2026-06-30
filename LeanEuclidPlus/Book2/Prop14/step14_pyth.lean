import SystemE
import Book.Prop47
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- The equation |h─e|² + |e─g|² = |g─h|². Unconditional construction ⟹ case-split on E = G:
--   • E = G (BE = ED): degenerate, the identity is segment symmetry (no triangle);
--   • E ≠ G: ∠g:e:h = ∟ (transfer from ∠b₀:e:h = ∟ since G on BE, H off BE), then Pythagoras
--     (proposition_47) on the right triangle E:H:G.
theorem helper_2_14_step14_pyth (e b₀ g h f : Point) (BE GH ED : Line)
    (h_eBE : e.onLine BE) (h_b0BE : b₀.onLine BE) (h_fBE : f.onLine BE)
    (h_gGH : g.onLine GH) (h_hGH : h.onLine GH)
    (h_eED : e.onLine ED) (h_hED : h.onLine ED)
    (h_bef : between b₀ e f) (h_bgf : between b₀ g f)
    (h_rt0 : ∠ b₀:e:h = ∟) (h_hoffBE : ¬ h.onLine BE) :
    |(h─e)| * |(h─e)| + |(e─g)| * |(e─g)| = |(g─h)| * |(g─h)| := by
  by_cases heg : e = g
  · euclid_finish
  · have hgBE : g.onLine BE := by euclid_finish
    have hperp : ∠ g:e:h = ∟ := by euclid_finish
    have htri : formTriangle e h g ED GH BE := by
      unfold formTriangle
      repeat' constructor
      all_goals (first | assumption | euclid_finish)
    euclid_apply (Elements.Book1.proposition_47 e h g ED GH BE)
    euclid_finish

end Elements.Book2
