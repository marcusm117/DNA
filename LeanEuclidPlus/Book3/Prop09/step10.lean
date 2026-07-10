import SystemE
import Book1.Prop08.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_9_step10
    (ABC : Circle) (b c d f : Point) (BC HL : Line)
    (hb_ABC : b.onCircle ABC) (hc_ABC : c.onCircle ABC)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hf_HL : f.onLine HL) (hd_HL : d.onLine HL)
    (hbfc : between b f c) (hbf_fc : |(b─f)| = |(f─c)|)
    (hd_inside : d.insideCircle ABC)
    (hd_bc : |(d─b)| = |(d─c)|)
    (hf_ne_d : f ≠ d)
    : ∀ o : Point, o.isCentre ABC → o.onLine HL := by
  have hf_BC : f.onLine BC := between_same_line_in b f c BC ⟨hbfc, hb_BC, hc_BC⟩
  have hbf : b ≠ f := by euclid_finish
  have hcf : c ≠ f := by euclid_finish
  have hd_off_BC : ¬d.onLine BC := by
    intro hdBC
    have hb_ne_c : b ≠ c := by euclid_finish
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
    linarith [segment_symmetric d b, segment_symmetric d c, hd_bc]
  have hangle_eq : ∠ b:f:d = ∠ c:f:d :=
    proposition_8 f b d f c d FB DB HL FC DC HL
      ⟨hform_fbd, hform_fcd, hfb_fc, rfl, hbd_cd⟩
  have hangle_symm : ∠ b:f:d = ∠ d:f:c :=
    hangle_eq.trans (angle_symm c f d ⟨hcf, hf_ne_d⟩)
  have hperp_bfd : ∠ b:f:d = ∟ :=
    perpendicular_if b c f d BC ⟨hb_BC, hc_BC, hbfc, hd_off_BC, hangle_symm⟩
  intro o ho
  have hoc_ob : |(o─c)| = |(o─b)| := point_on_circle_onlyif o b c ABC ⟨ho, hb_ABC, hc_ABC⟩
  by_cases h_of : o = f
  · exact h_of ▸ hf_HL
  · have ho_off_BC : ¬o.onLine BC := by
      intro hoBC
      have hbetween : between b o c := by euclid_finish
      have hob_oc : |(o─b)| = |(o─c)| := hoc_ob.symm
      have heq : o = f := by
        have h1 := between_if b f c hbfc
        have h2 := between_if b o c hbetween
        have h3 := segment_symmetric b f
        have h4 := segment_symmetric c f
        have h5 := segment_symmetric o b
        have h6 := segment_symmetric o c
        euclid_finish
      exact h_of heq
    obtain ⟨OF, ho_OF, hf_OF⟩ := line_from_points o f h_of
    have hob : o ≠ b := by euclid_finish
    have hoc : o ≠ c := by euclid_finish
    obtain ⟨OB, ho_OB, hb_OB⟩ := line_from_points o b hob
    obtain ⟨OC, ho_OC, hc_OC⟩ := line_from_points o c hoc
    have hform_fob : formTriangle f o b OF OB BC := by euclid_finish
    have hform_foc : formTriangle f o c OF OC BC := by euclid_finish
    have hob_oc : |(o─b)| = |(o─c)| := hoc_ob.symm
    have hstep_angle : ∠ o:f:b = ∠ o:f:c :=
      proposition_8 f o b f o c OF OB BC OF OC BC
        ⟨hform_fob, hform_foc, rfl, hfb_fc, hob_oc⟩
    have hangle_ao : ∠ b:f:o = ∠ o:f:b := (angle_symm o f b ⟨h_of, hbf.symm⟩).symm
    have hstep5' : ∠ b:f:o = ∠ o:f:c := hangle_ao.trans hstep_angle
    have hperp_o : ∠ b:f:o = ∟ :=
      perpendicular_if b c f o BC ⟨hb_BC, hc_BC, hbfc, ho_off_BC, hstep5'⟩
    have hd_fc : ∠ d:f:c = ∟ := by
      have := perpendicular_onlyif b c f d BC ⟨hb_BC, hc_BC, hbfc, hd_off_BC, hperp_bfd⟩
      linarith
    have ho_fc : ∠ o:f:c = ∟ := by
      have := perpendicular_onlyif b c f o BC ⟨hb_BC, hc_BC, hbfc, ho_off_BC, hperp_o⟩
      linarith
    have hflat : ∠ b:f:c = ∟ + ∟ := flat_angle_onlyif b f c hbfc
    euclid_finish

end Elements.Book3
