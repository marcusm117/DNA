import SystemE

namespace Elements.Book1

theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
by
  euclid_intros
  euclid_apply circle_from_points a b as BCD
  euclid_apply circle_from_points b a as ACE
  euclid_apply intersection_circles BCD ACE as c
  euclid_apply point_on_circle_onlyif a b c BCD
  euclid_apply point_on_circle_onlyif b a c ACE
  use c
  euclid_finish

/-
The same theorem as `proposition_1`, but written WITHOUT any custom tactics
(`euclid_intros`, `euclid_apply`, `euclid_finish`) -- only `intro`, `obtain`,
`have`, `refine`, `rw`, `exact`, and the raw System E axioms. This makes every
step that the custom tactics normally hide completely explicit.
-/
-- #print distinctPointsOnLine
-- theorem proposition_1_test : ∀ (a b : Point) (AB : Line),
--   distinctPointsOnLine a b AB →
--   ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by
--   intro a b AB h1
--   -- `distinctPointsOnLine a b AB` is by definition `a.onLine AB ∧ b.onLine AB ∧ a ≠ b`.
--   -- Split it into its three pieces (this is what `euclid_intros` does automatically).
--   obtain ⟨_ha_on, _hb_on, hab⟩ := h1
--   -- Euclid, Post. 3: draw circle BCD with centre `a`, radius `ab`.
--   -- The axiom needs the proof `a ≠ b` (which is `hab`); it returns an *existential*,
--   -- so we `obtain` the circle and its two defining facts.
--   obtain ⟨BCD, ha_centre, hb_BCD⟩ := circle_from_points a b hab
--   -- Post. 3 again: circle ACE with centre `b`, radius `ba`. Needs `b ≠ a`, i.e. `hab.symm`.
--   obtain ⟨ACE, hb_centre, ha_ACE⟩ := circle_from_points b a hab.symm
--   -- The crux that `euclid_finish`/SMT proves implicitly: the two circles actually meet.
--   -- We discharge it by hand: each circle's centre lies inside the *other* circle
--   -- (`center_inside_circle`), which is exactly the premise of `intersection_circle_circle_2`.
--   have hInt : BCD.intersectsCircle ACE :=
--     intersection_circle_circle_2 b a BCD ACE
--       hb_BCD                                  -- b is on BCD
--       (center_inside_circle a BCD ha_centre)  -- a (centre of BCD) is inside BCD
--       (center_inside_circle b ACE hb_centre)  -- b (centre of ACE) is inside ACE
--       ha_ACE                                  -- a is on ACE
--   -- Post./construction: obtain the intersection point `c`, on both circles.
--   obtain ⟨c, hc_BCD, hc_ACE⟩ := intersection_circles BCD ACE hInt
--   -- Supply `c` as the witness and prove the two length equalities.
--   refine ⟨c, ?_, ?_⟩
--   · -- Goal: |(c─a)| = |(a─b)|.
--     -- BCD has centre a and contains both b and c, so radii ac and ab are equal.
--     have h : |(a─c)| = |(a─b)| :=
--       point_on_circle_onlyif a b c BCD ⟨ha_centre, hb_BCD, hc_BCD⟩
--     rw [segment_symmetric c a]   -- rewrite |(c─a)| as |(a─c)|
--     exact h
--   · -- Goal: |(c─b)| = |(a─b)|.
--     -- ACE has centre b and contains both a and c, so radii bc and ba are equal.
--     have h : |(b─c)| = |(b─a)| :=
--       point_on_circle_onlyif b a c ACE ⟨hb_centre, ha_ACE, hc_ACE⟩
--     rw [segment_symmetric c b]   -- goal becomes |(b─c)| = |(a─b)|
--     rw [h]                       -- goal becomes |(b─a)| = |(a─b)|
--     exact segment_symmetric b a


theorem proposition_1' : ∀ (a b x : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
by
  euclid_intros
  euclid_apply circle_from_points a b as BCD
  euclid_apply circle_from_points b a as ACE
  euclid_apply intersection_opposite_side BCD ACE x a b AB as c
  euclid_apply point_on_circle_onlyif a b c BCD
  euclid_apply point_on_circle_onlyif b a c ACE
  use c
  euclid_finish

end Elements.Book1
