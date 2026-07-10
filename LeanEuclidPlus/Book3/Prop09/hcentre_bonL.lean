import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_9_hcentre_bonL
    (ABC α₀ : Circle)
    (b c d f o : Point)
    (BC L : Line)
    (hb : b.onCircle ABC)
    (hc : c.onCircle ABC)
    (h_db_dc : |(d─b)| = |(d─c)|)
    (hb_BC : b.onLine BC)
    (hc_BC : c.onLine BC)
    (hbc : b ≠ c)
    (hbfc : between b f c)
    (hbf_fc : |(b─f)| = |(f─c)|)
    (ho : o.isCentre ABC)
    (hdo : ¬d = o)
    (hd_ctr : d.isCentre α₀)
    (hb_α₀ : b.onCircle α₀) (hc_α₀ : c.onCircle α₀)
    (hd_L : d.onLine L)
    (ho_L : o.onLine L)
    (hbL : b.onLine L)
    : False := by
  have hf_BC : f.onLine BC := between_same_line_in b f c BC ⟨hbfc, hb_BC, hc_BC⟩
  have hd_in_α₀ : d.insideCircle α₀ := center_inside_circle d α₀ hd_ctr
  have ho_in_ABC : o.insideCircle ABC := center_inside_circle o ABC ho
  have hdb : d ≠ b := by euclid_finish
  have hdc : d ≠ c := by euclid_finish
  by_cases hdBC : d.onLine BC
  · -- d on BC → L = BC → circle_line_intersections → d = o → contradiction
    have hLBC : L = BC :=
      two_points_determine_line b d L BC ⟨⟨hbL, hd_L, hdb.symm⟩, hb_BC, hdBC⟩
    have hc_L : c.onLine L := hLBC ▸ hc_BC
    have hbet_bdc : between b d c :=
      circle_line_intersections d b c L α₀ ⟨hd_L, hbL, hc_L, hd_in_α₀, hb_α₀, hc_α₀, hbc⟩
    have hbet_boc : between b o c :=
      circle_line_intersections o b c L ABC ⟨ho_L, hbL, hc_L, ho_in_ABC, hb, hc, hbc⟩
    have hbetd := between_if b d c hbet_bdc
    have hbeto := between_if b o c hbet_boc
    have hob_oc : |(o─b)| = |(o─c)| := by
      linarith [point_on_circle_onlyif o b c ABC ⟨ho, hb, hc⟩]
    have hdo' : d = o := by euclid_finish
    exact hdo hdo'
  · -- d not on BC → SSS perpendicular bisector of BC at f → then L = BC → contradiction
    have hfd : f ≠ d := by euclid_finish
    obtain ⟨HL, hf_HL, hd_HL⟩ := line_from_points f d hfd
    obtain ⟨BD, hb_BD, hd_BD⟩ := line_from_points b d hdb.symm
    obtain ⟨CD, hc_CD, hd_CD⟩ := line_from_points c d hdc.symm
    have hbf : b ≠ f := by euclid_finish
    have hcf : c ≠ f := by euclid_finish
    have hform_fbd : formTriangle f b d BC BD HL := by euclid_finish
    have hform_fcd : formTriangle f c d BC CD HL := by euclid_finish
    have hfb_fc : |(f─b)| = |(f─c)| := by linarith [segment_symmetric b f, hbf_fc]
    have hbd_cd : |(b─d)| = |(c─d)| := by
      linarith [segment_symmetric d b, segment_symmetric d c, h_db_dc]
    have h5 : ∠b:f:d = ∠c:f:d := by
      euclid_apply (proposition_8 f b d f c d BC BD HL BC CD HL ⟨hform_fbd, hform_fcd, hfb_fc, rfl, hbd_cd⟩)
    have h5' : ∠b:f:d = ∠d:f:c := h5.trans (angle_symm c f d ⟨hcf, hfd⟩)
    have hperp_d : ∠b:f:d = ∟ :=
      perpendicular_if b c f d BC ⟨hb_BC, hc_BC, hbfc, hdBC, h5'⟩
    by_cases hoBC : o.onLine BC
    · -- o on BC → L = BC → d.onLine BC → contradiction
      have hob : b ≠ o := by euclid_finish
      have hLBC : L = BC :=
        two_points_determine_line b o L BC ⟨⟨hbL, ho_L, hob⟩, hb_BC, hoBC⟩
      exact hdBC (hLBC ▸ hd_L)
    · -- o not on BC → SSS gives ∠b:f:o = ∟ → o on HL → HL = L → f on L → L = BC → contradiction
      have hof : f ≠ o := by euclid_finish
      obtain ⟨OHL, hf_OHL, ho_OHL⟩ := line_from_points f o hof
      have hob : b ≠ o := by euclid_finish
      obtain ⟨BO, hb_BO, ho_BO⟩ := line_from_points b o hob
      have hco : c ≠ o := by euclid_finish
      obtain ⟨CO, hc_CO, ho_CO⟩ := line_from_points c o hco
      have hform_fbo : formTriangle f b o BC BO OHL := by euclid_finish
      have hform_fco : formTriangle f c o BC CO OHL := by euclid_finish
      have hob_oc : |(o─b)| = |(o─c)| := by
        linarith [point_on_circle_onlyif o b c ABC ⟨ho, hb, hc⟩]
      have hbo_co : |(b─o)| = |(c─o)| := by
        linarith [segment_symmetric o b, segment_symmetric o c, hob_oc]
      have h6 : ∠b:f:o = ∠c:f:o := by
        euclid_apply (proposition_8 f b o f c o BC BO OHL BC CO OHL ⟨hform_fbo, hform_fco, hfb_fc, rfl, hbo_co⟩)
      have h6' : ∠b:f:o = ∠o:f:c := h6.trans (angle_symm c f o ⟨hcf, hof⟩)
      have hperp_o : ∠b:f:o = ∟ :=
        perpendicular_if b c f o BC ⟨hb_BC, hc_BC, hbfc, hoBC, h6'⟩
      have ho_HL : o.onLine HL := by euclid_finish
      have hHLL : HL = L :=
        two_points_determine_line d o HL L ⟨⟨hd_HL, ho_HL, hdo⟩, hd_L, ho_L⟩
      have hf_L : f.onLine L := hHLL ▸ hf_HL
      have hLBC : L = BC :=
        two_points_determine_line b f L BC ⟨⟨hbL, hf_L, hbf⟩, hb_BC, hf_BC⟩
      exact hdBC (hLBC ▸ hd_L)

end Elements.Book3
