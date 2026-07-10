import SystemE
import Book1.Prop08.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_9_step9_assumption1
    (ABC : Circle) (a b d e : Point) (AB GK : Line)
    (ha_ABC : a.onCircle ABC) (hb_ABC : b.onCircle ABC)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (he_GK : e.onLine GK) (hd_GK : d.onLine GK)
    (haeb : between a e b)
    (he_ne_d : e ≠ d)
    (hd_inside : d.insideCircle ABC)
    (hstep4 : |(d─a)| = |(d─b)|)
    : e.onLine GK ∧ between a e b ∧ |(a─e)| = |(e─b)| ∧ ∠ a:e:d = ∟ → ∀ o : Point, o.isCentre ABC → o.onLine GK := by
  intro ⟨_, _, hae_eb, hperp⟩ o ho
  have he_AB : e.onLine AB := between_same_line_in a e b AB ⟨haeb, ha_AB, hb_AB⟩
  have hob_oa : |(o─b)| = |(o─a)| := point_on_circle_onlyif o a b ABC ⟨ho, ha_ABC, hb_ABC⟩
  have hae : a ≠ e := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  -- Derive ¬d.onLine AB via circle_line_intersections + midpoint uniqueness
  have hd_off_AB : ¬d.onLine AB := by
    intro hdAB
    have ha_ne_b : a ≠ b := by euclid_finish
    have hbet_adb : between a d b :=
      circle_line_intersections d a b AB ABC ⟨hdAB, ha_AB, hb_AB, hd_inside, ha_ABC, hb_ABC, ha_ne_b⟩
    have heq : d = e := by
      have h1 := between_if a d b hbet_adb
      have h2 := between_if a e b haeb
      have h3 := segment_symmetric d a
      have h4 := segment_symmetric d b
      have h5 := segment_symmetric a e
      have h6 := segment_symmetric e b
      euclid_finish
    exact he_ne_d heq.symm
  by_cases h_oe : o = e
  · exact h_oe ▸ he_GK
  · have ho_off_AB : ¬o.onLine AB := by
      intro hoAB
      have hbetween : between a o b := by euclid_finish
      have hoa_ob : |(o─a)| = |(o─b)| := hob_oa.symm
      have heq : o = e := by
        have h1 := between_if a e b haeb
        have h2 := between_if a o b hbetween
        have h3 := segment_symmetric a e
        have h4 := segment_symmetric b e
        have h5 := segment_symmetric o a
        have h6 := segment_symmetric o b
        euclid_finish
      exact h_oe heq
    obtain ⟨OE, ho_OE, he_OE⟩ := line_from_points o e h_oe
    have hoa : o ≠ a := by euclid_finish
    have hob : o ≠ b := by euclid_finish
    obtain ⟨OA, ho_OA, ha_OA⟩ := line_from_points o a hoa
    obtain ⟨OB, ho_OB, hb_OB⟩ := line_from_points o b hob
    -- formTriangle e o a: OE through (e,o), OA through (o,a), AB through (e,a)
    have hform_eoa : formTriangle e o a OE OA AB := by euclid_finish
    -- formTriangle e o b: OE through (e,o), OB through (o,b), AB through (e,b)
    have hform_eob : formTriangle e o b OE OB AB := by euclid_finish
    have hoa_ob : |(o─a)| = |(o─b)| := hob_oa.symm
    have hea_eb : |(e─a)| = |(e─b)| := by
      linarith [segment_symmetric a e, segment_symmetric e b, hae_eb]
    -- SSS: triangles eoa ≅ eob → ∠o:e:a = ∠o:e:b
    have hstep_angle : ∠ o:e:a = ∠ o:e:b :=
      proposition_8 e o a e o b OE OA AB OE OB AB
        ⟨hform_eoa, hform_eob, rfl, hea_eb, hoa_ob⟩
    -- ∠a:e:o = ∠o:e:a (angle symmetry) → ∠a:e:o = ∠o:e:b
    have hangle_ao : ∠ a:e:o = ∠ o:e:a := (angle_symm o e a ⟨h_oe, hae.symm⟩).symm
    have hstep5' : ∠ a:e:o = ∠ o:e:b := hangle_ao.trans hstep_angle
    -- Perpendicular: ∠a:e:o = ∟
    have hperp_o : ∠ a:e:o = ∟ :=
      perpendicular_if a b e o AB ⟨ha_AB, hb_AB, haeb, ho_off_AB, hstep5'⟩
    -- Both GK and OE are perpendicular to AB at e; derive additional angle facts
    have hd_eb : ∠ d:e:b = ∟ := by
      have := perpendicular_onlyif a b e d AB ⟨ha_AB, hb_AB, haeb, hd_off_AB, hperp⟩
      linarith
    have ho_eb : ∠ o:e:b = ∟ := by
      have := perpendicular_onlyif a b e o AB ⟨ha_AB, hb_AB, haeb, ho_off_AB, hperp_o⟩
      linarith
    have hflat : ∠ a:e:b = ∟ + ∟ := flat_angle_onlyif a e b haeb
    -- SMT with full angle context: both d and o on the unique perpendicular to AB at e
    euclid_finish

end Elements.Book3
