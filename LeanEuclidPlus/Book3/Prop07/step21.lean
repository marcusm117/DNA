import SystemE
import Book1.Prop04.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step21
    (ABCD : Circle) (a d e f g h : Point) (AD GE EH FH : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD)
    (hg : g.onCircle ABCD) (hh_on : h.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    (heEH : e.onLine EH) (hhEH : h.onLine EH)
    (hfFH : f.onLine FH) (hhFH : h.onLine FH)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hg_ne_a : g ≠ a) (hg_ne_d : g ≠ d)
    (step19_assumption1 : |(e─g)| = |(e─h)|)
    (step20 : ∠ g:e:f = ∠ h:e:f)
    : |(f─g)| = |(f─h)| := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have he_inside : e.insideCircle ABCD := by euclid_finish
  have hef : e ≠ f := by euclid_finish
  -- g is off AD
  have hgAD : ¬(g.onLine AD) := by
    intro hgon
    have := circle_line_intersections e g d AD ABCD ⟨heAD, hgon, hdAD, he_inside, hg, hd, hg_ne_d⟩
    exact hg_ne_a (by euclid_finish)
  -- h is off AD
  have hhAD : ¬(h.onLine AD) := by euclid_finish
  -- Line through g and f
  euclid_apply (line_from_points g f) as GF
  have hgGF : g.onLine GF := by euclid_finish
  have hfGF : f.onLine GF := by euclid_finish
  have heg : e ≠ g := fun heq => hgAD (heq ▸ heAD)
  have heh : e ≠ h := by euclid_finish
  -- ¬(f.onLine GE): if f on GE and e on GE and f on AD and e on AD with e≠f → GE=AD → g on AD
  have hfGE : ¬(f.onLine GE) := by
    intro hfon
    have : GE = AD := two_points_determine_line e f GE AD ⟨⟨heGE, hfon, hef⟩, heAD, hfAD⟩
    rw [this] at hgGE; exact hgAD hgGE
  -- ¬(f.onLine EH): similarly h off AD, EH through e and h
  have hfEH : ¬(f.onLine EH) := by
    intro hfon
    have : EH = AD := two_points_determine_line e f EH AD ⟨⟨heEH, hfon, hef⟩, heAD, hfAD⟩
    rw [this] at hhEH; exact hhAD hhEH
  have hGE_ne_GF : GE ≠ GF := fun heq => hfGE (heq ▸ hfGF)
  have hGF_ne_AD : GF ≠ AD := fun heq => hgAD (heq ▸ hgGF)
  have hCA_ne_GE : AD ≠ GE := fun heq => hfGE (heq.symm ▸ hfAD)
  have hEH_ne_FH : EH ≠ FH := fun heq => hfEH (heq ▸ hfFH)
  have hFH_ne_AD : FH ≠ AD := fun heq => hhAD (heq ▸ hhFH)
  have hCA_ne_EH : AD ≠ EH := fun heq => hfEH (heq.symm ▸ hfAD)
  have htri1 : formTriangle e g f GE GF AD :=
    ⟨⟨heGE, hgGE, heg⟩, hgGF, hfGF, hfAD, heAD, hGE_ne_GF, hGF_ne_AD, hCA_ne_GE⟩
  have htri2 : formTriangle e h f EH FH AD :=
    ⟨⟨heEH, hhEH, heh⟩, hhFH, hfFH, hfAD, heAD, hEH_ne_FH, hFH_ne_AD, hCA_ne_EH⟩
  euclid_apply (Elements.Book1.proposition_4 e g f e h f GE GF AD EH FH AD)
  linarith [segment_symmetric g f, segment_symmetric h f]

end Elements.Book3
