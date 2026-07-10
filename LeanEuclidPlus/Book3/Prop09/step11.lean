import SystemE
import Book1.Prop08.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_9_step11
    (ABC : Circle) (a b c d e f : Point) (AB BC GK HL : Line)
    -- circle membership
    (ha_ABC : a.onCircle ABC) (hb_ABC : b.onCircle ABC) (hc_ABC : c.onCircle ABC)
    (hd_inside : d.insideCircle ABC)
    -- line membership
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (he_GK : e.onLine GK) (hd_GK : d.onLine GK)
    (hf_HL : f.onLine HL) (hd_HL : d.onLine HL)
    -- betweenness / midpoint of AB
    (haeb : between a e b) (hae_eb : |(a─e)| = |(e─b)|)
    -- betweenness / midpoint of BC
    (hbfc : between b f c) (hbf_fc : |(b─f)| = |(f─c)|)
    -- equal radii
    (hda_db : |(d─a)| = |(d─b)|) (hdb_dc : |(d─b)| = |(d─c)|)
    -- perpendicular bisector of AB (step8)
    (hperp_e : ∠ a:e:d = ∟)
    -- distinctness
    (he_ne_d : e ≠ d) (hf_ne_d : f ≠ d)
    (ha_ne_b : a ≠ b) (hb_ne_c : b ≠ c) (ha_ne_c : a ≠ c)
    : ∀ p : Point, p.onLine GK → p.onLine HL → p = d := by
  -- First prove ∠b:f:d = ∟ (perpendicular bisector of BC), using SSS exactly as step10 does.
  have hf_BC : f.onLine BC := between_same_line_in b f c BC ⟨hbfc, hb_BC, hc_BC⟩
  have hbf : b ≠ f := by euclid_finish
  have hcf : c ≠ f := by euclid_finish
  have hd_off_BC : ¬d.onLine BC := by
    intro hdBC
    have hbet_bdc : between b d c :=
      circle_line_intersections d b c BC ABC ⟨hdBC, hb_BC, hc_BC, hd_inside, hb_ABC, hc_ABC, hb_ne_c⟩
    have heq : d = f := by
      have h1 := between_if b d c hbet_bdc
      have h2 := between_if b f c hbfc
      have h3 := segment_symmetric d b
      have h4 := segment_symmetric d c
      have h5 := segment_symmetric b f
      have h6 := segment_symmetric f c
      euclid_finish
    exact hf_ne_d heq.symm
  obtain ⟨FB, hf_FB, hb_FB⟩ := line_from_points f b hbf.symm
  obtain ⟨FC, hf_FC, hc_FC⟩ := line_from_points f c hcf.symm
  have hdb : d ≠ b := by euclid_finish
  have hdc : d ≠ c := by euclid_finish
  obtain ⟨DB, hd_DB, hb_DB⟩ := line_from_points d b hdb
  obtain ⟨DC, hd_DC, hc_DC⟩ := line_from_points d c hdc
  have hform_fbd : formTriangle f b d FB DB HL := by euclid_finish
  have hform_fcd : formTriangle f c d FC DC HL := by euclid_finish
  have hfb_fc : |(f─b)| = |(f─c)| := by
    linarith [segment_symmetric b f, hbf_fc]
  have hbd_cd : |(b─d)| = |(c─d)| := by
    linarith [segment_symmetric d b, segment_symmetric d c, hdb_dc]
  have hangle_eq : ∠ b:f:d = ∠ c:f:d :=
    proposition_8 f b d f c d FB DB HL FC DC HL
      ⟨hform_fbd, hform_fcd, hfb_fc, rfl, hbd_cd⟩
  have hperp_f : ∠ b:f:d = ∟ :=
    perpendicular_if b c f d BC ⟨hb_BC, hc_BC, hbfc, hd_off_BC,
      hangle_eq.trans (angle_symm c f d ⟨hcf, hf_ne_d⟩)⟩
  -- Main proof: p on GK ∩ HL → p = d
  intro p hp_GK hp_HL
  by_cases h_pd : p = d
  · exact h_pd
  · exfalso
    -- p ≠ d, so two_points_determine_line gives GK = HL
    have hGK_HL : GK = HL :=
      two_points_determine_line p d GK HL ⟨⟨hp_GK, hd_GK, h_pd⟩, hp_HL, hd_HL⟩
    -- Now f is on GK (since f on HL = GK)
    have hf_GK : f.onLine GK := hGK_HL ▸ hf_HL
    -- e on AB
    have he_AB : e.onLine AB := between_same_line_in a e b AB ⟨haeb, ha_AB, hb_AB⟩
    -- GK ⊥ AB at e (hperp_e) and HL = GK ⊥ BC at f (hperp_f).
    -- Both perpendiculars to GK pass through b, so AB = BC, and a.onLine BC.
    -- Then a, b, c on BC with a ≠ c and all on circle: derive contradiction.
    have hperp_f_bc : ∠ b:f:d = ∟ := hperp_f
    -- With GK = HL and d on GK: all geometric constraints now live on one line.
    -- SMT closes from: both right angles + midpoints + equal radii + distinctness.
    euclid_finish

end Elements.Book3
