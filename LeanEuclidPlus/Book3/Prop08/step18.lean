import SystemE
import Book1.Prop24.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- |DL| < |DH|: same argument as step15 but for l,h.
-- |m─h| = |m─l| (radii), ∠h:m:d > ∠l:m:d → Prop 24 gives |h─d| > |l─d|.
-- hex_hf packages the far-circle-partner for h as an existential Prop binder (not an object):
-- SP finds it as the intro'd but undestucted ∃ hf hyp in Main's context.
theorem helper_3_8_step18
    (ABC : Circle) (m k l d h g a : Point) (ML LD MH AG : Line)
    (hm : m.isCentre ABC)
    (hdnotCircle : ¬d.onCircle ABC) (hdnotInside : ¬d.insideCircle ABC)
    (hl : l.onCircle ABC) (hh : h.onCircle ABC)
    (hg : g.onCircle ABC) (ha : a.onCircle ABC)
    (hgAG : g.onLine AG) (haAG : a.onLine AG) (hdAG : d.onLine AG)
    (hbet_dgm : between d g m) (hbet_gma : between g m a)
    (hne_hg : h ≠ g) (hne_ag : a ≠ g)
    (hMHm : m.onLine MH) (hMHh : h.onLine MH) (hne_mh : m ≠ h)
    (hangle_lh : ∠l:m:d < ∠h:m:d)
    (hex_hf : ∃ p : Point, p.onCircle ABC ∧ between d h p)
    (hassump1 : formTriangle m l d ML LD AG ∧ d.sameSide k ML ∧ l.sameSide k AG) :
    |(d─l)| < |(d─h)| := by
  obtain ⟨hw, hhw, hbetdhw⟩ := hex_hf
  have hft_l := hassump1.1
  have hmAG : m.onLine AG := hft_l.2.2.2.2.1
  -- |m─h| = |m─l| (radii)
  have hradius : |(m─l)| = |(m─h)| := point_on_circle_onlyif m h l ABC ⟨hm, hh, hl⟩
  -- h ≠ d (h on circle, d not)
  have hne_hd : h ≠ d := by euclid_finish
  -- ¬h.onLine AG: between d h hw with hw on circle; if h on AG then h=g or h=a;
  --   h≠g so h=a; but between d a hw with hw on circle on AG → hw=g or hw=a → both contradict.
  have hhoffAG : ¬h.onLine AG := by euclid_finish
  -- Introduce line HD
  obtain ⟨HD, hhHD, hdHD⟩ := line_from_points h d hne_hd
  -- formTriangle m h d MH HD AG
  have hft_h : formTriangle m h d MH HD AG := by euclid_finish
  -- Prop I.24: ∠h:m:d > ∠l:m:d, equal radii → |h─d| > |l─d|
  have hld_lt_hd : |(h─d)| > |(l─d)| :=
    Elements.Book1.proposition_24 m h d m l d MH HD AG ML LD AG
      ⟨hft_h, hft_l, hradius.symm, rfl, by linarith⟩
  linarith [segment_symmetric h d, segment_symmetric l d]

end Elements.Book3
