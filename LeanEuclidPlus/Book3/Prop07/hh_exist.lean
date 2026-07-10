import SystemE
import Book1.Prop08.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_hh_exist
    (ABCD : Circle) (a b c d e f g : Point) (AD GE : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hg : g.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hg_ne_a : g ≠ a) (hg_ne_d : g ≠ d)
    (step4 : |(f─a)| > |(f─b)|)
    (step7 : |(b─f)| > |(c─f)|)
    (step9 : |(f─c)| > |(f─g)|)
    : ∃ h : Point, h.onCircle ABCD ∧ ∠ f:e:h = ∠ g:e:f ∧ h ≠ g := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have hef : e ≠ f := by euclid_finish
  have he_inside : e.insideCircle ABCD := center_inside_circle e ABCD h_ctr
  have hgAD : ¬(g.onLine AD) := by
    intro hgon
    have hbgd := circle_line_intersections e g d AD ABCD ⟨heAD, hgon, hdAD, he_inside, hg, hd, hg_ne_d⟩
    exact hg_ne_a (by euclid_finish)
  have heg : e ≠ g := fun heq => hgAD (heq ▸ heAD)
  have hfg : f ≠ g := fun heq => hgAD (heq ▸ hfAD)
  obtain ⟨β, hβ_ctr, hgβ⟩ := circle_from_points f g hfg
  have hne : ABCD ≠ β := fun heq => hef (centre_unique e f ABCD ⟨h_ctr, heq ▸ hβ_ctr⟩)
  have hf_β : f.insideCircle β := center_inside_circle f β hβ_ctr
  have haβ : a.outsideCircle β := by euclid_finish
  have hfno : ¬(f.outsideCircle ABCD) := by euclid_finish
  have hano : ¬(a.outsideCircle ABCD) := by euclid_finish
  have hinters : ABCD.intersectsCircle β :=
    intersection_circle_circle_1 f a ABCD β ⟨hfno, hano, hf_β, haβ⟩
  obtain ⟨h, hh_ABCD, hh_β, hh_opp⟩ :=
    intersection_opposite_side ABCD β g e f AD ⟨hinters, h_ctr, hβ_ctr, heAD, hfAD, hgAD⟩
  have hh_ne_g : h ≠ g := fun heq =>
    hh_opp.2.2 (heq ▸ same_side_rfl g AD hgAD)
  have hfh : |(f─h)| = |(f─g)| :=
    point_on_circle_onlyif f g h β ⟨hβ_ctr, hgβ, hh_β⟩
  have heh_eq : |(e─h)| = |(e─g)| :=
    point_on_circle_onlyif e g h ABCD ⟨h_ctr, hg, hh_ABCD⟩
  have hhAD : ¬(h.onLine AD) := hh_opp.1
  have hhe : h ≠ e := fun heq => hhAD (heq ▸ heAD)
  euclid_apply (line_from_points e h) as EH
  have heEH : e.onLine EH := by euclid_finish
  have hhEH : h.onLine EH := by euclid_finish
  euclid_apply (line_from_points f h) as FH
  have hfFH : f.onLine FH := by euclid_finish
  have hhFH : h.onLine FH := by euclid_finish
  euclid_apply (line_from_points g f) as GF
  have hgGF : g.onLine GF := by euclid_finish
  have hfGF : f.onLine GF := by euclid_finish
  have hfGE : ¬(f.onLine GE) := by
    intro hfon
    exact hgAD (two_points_determine_line e f GE AD ⟨⟨heGE, hfon, hef⟩, heAD, hfAD⟩ ▸ hgGE)
  have hfEH : ¬(f.onLine EH) := by
    intro hfon
    exact hhAD (two_points_determine_line e f EH AD ⟨⟨heEH, hfon, hef⟩, heAD, hfAD⟩ ▸ hhEH)
  have hGE_ne_GF : GE ≠ GF := fun heq => hfGE (heq ▸ hfGF)
  have hGF_ne_AD : GF ≠ AD := fun heq => hgAD (heq ▸ hgGF)
  have hAD_ne_GE : AD ≠ GE := fun heq => hfGE (heq.symm ▸ hfAD)
  have hEH_ne_FH : EH ≠ FH := fun heq => hfEH (heq ▸ hfFH)
  have hFH_ne_AD : FH ≠ AD := fun heq => hhAD (heq ▸ hhFH)
  have hAD_ne_EH : AD ≠ EH := fun heq => hfEH (heq.symm ▸ hfAD)
  have htri_g : formTriangle e g f GE GF AD :=
    ⟨⟨heGE, hgGE, heg⟩, hgGF, hfGF, hfAD, heAD, hGE_ne_GF, hGF_ne_AD, hAD_ne_GE⟩
  have htri_h : formTriangle e h f EH FH AD :=
    ⟨⟨heEH, hhEH, fun heq => hhe heq.symm⟩, hhFH, hfFH, hfAD, heAD, hEH_ne_FH, hFH_ne_AD, hAD_ne_EH⟩
  have hgf_eq : |(g─f)| = |(h─f)| := by
    have hss := segment_symmetric g f
    have hsh := segment_symmetric h f
    linarith
  have hangle8 := Elements.Book1.proposition_8 e g f e h f GE GF AD EH FH AD
    ⟨htri_g, htri_h, heh_eq.symm, rfl, hgf_eq⟩
  have hangle : ∠ f:e:h = ∠ g:e:f :=
    (angle_symm h e f ⟨hhe, hef⟩).symm.trans hangle8.symm
  exact ⟨h, hh_ABCD, hangle, hh_ne_g⟩

end Elements.Book3
