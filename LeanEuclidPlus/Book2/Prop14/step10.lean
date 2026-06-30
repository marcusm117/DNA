import SystemE

namespace Elements.Book2

-- step 10: GH is a genuine line through the two distinct points g, h. g ≠ h because |g─h| = |g─b₀|
-- and b₀ ≠ g (g is between b₀ and f), so the common radius is positive.
set_option systemE.solverTime 30 in
theorem helper_2_14_step10 (g h b₀ f : Point) (GH : Line)
    (h_gGH : g.onLine GH) (h_hGH : h.onLine GH)
    (h_rad : |(g─h)| = |(g─b₀)|) (h_bet : between b₀ g f) :
    distinctPointsOnLine g h GH := by
  euclid_finish

end Elements.Book2
